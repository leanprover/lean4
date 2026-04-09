// Lean compiler output
// Module: Lake.Config.Meta
// Imports: public import Lake.Util.Binder public import Lake.Config.MetaClasses public meta import Lake.Util.Binder public meta import Lean.Parser.Command public meta import Lake.Util.Name import Lean.Parser.Command
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lake_expandBinders(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkDepArrow(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
static const lean_string_object l_Lake_configField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "configField"};
static const lean_object* l_Lake_configField___closed__0 = (const lean_object*)&l_Lake_configField___closed__0_value;
static const lean_string_object l_Lake_configField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_configField___closed__1 = (const lean_object*)&l_Lake_configField___closed__1_value;
static const lean_ctor_object l_Lake_configField___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_configField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__2_value_aux_0),((lean_object*)&l_Lake_configField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 254, 146, 249, 6, 137, 67, 241)}};
static const lean_object* l_Lake_configField___closed__2 = (const lean_object*)&l_Lake_configField___closed__2_value;
static const lean_string_object l_Lake_configField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_configField___closed__3 = (const lean_object*)&l_Lake_configField___closed__3_value;
static const lean_ctor_object l_Lake_configField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_configField___closed__4 = (const lean_object*)&l_Lake_configField___closed__4_value;
static const lean_string_object l_Lake_configField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lake_configField___closed__5 = (const lean_object*)&l_Lake_configField___closed__5_value;
static const lean_ctor_object l_Lake_configField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lake_configField___closed__6 = (const lean_object*)&l_Lake_configField___closed__6_value;
static const lean_string_object l_Lake_configField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "nestedDeclModifiers"};
static const lean_object* l_Lake_configField___closed__7 = (const lean_object*)&l_Lake_configField___closed__7_value;
static const lean_ctor_object l_Lake_configField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__7_value),LEAN_SCALAR_PTR_LITERAL(80, 42, 11, 81, 100, 8, 187, 212)}};
static const lean_object* l_Lake_configField___closed__8 = (const lean_object*)&l_Lake_configField___closed__8_value;
static const lean_ctor_object l_Lake_configField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configField___closed__8_value)}};
static const lean_object* l_Lake_configField___closed__9 = (const lean_object*)&l_Lake_configField___closed__9_value;
static const lean_string_object l_Lake_configField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_configField___closed__10 = (const lean_object*)&l_Lake_configField___closed__10_value;
static const lean_ctor_object l_Lake_configField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_configField___closed__11 = (const lean_object*)&l_Lake_configField___closed__11_value;
static const lean_string_object l_Lake_configField___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_configField___closed__12 = (const lean_object*)&l_Lake_configField___closed__12_value;
static const lean_ctor_object l_Lake_configField___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__12_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_configField___closed__13 = (const lean_object*)&l_Lake_configField___closed__13_value;
static const lean_ctor_object l_Lake_configField___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configField___closed__13_value)}};
static const lean_object* l_Lake_configField___closed__14 = (const lean_object*)&l_Lake_configField___closed__14_value;
static const lean_string_object l_Lake_configField___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l_Lake_configField___closed__15 = (const lean_object*)&l_Lake_configField___closed__15_value;
static const lean_ctor_object l_Lake_configField___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_configField___closed__15_value)}};
static const lean_object* l_Lake_configField___closed__16 = (const lean_object*)&l_Lake_configField___closed__16_value;
static const lean_ctor_object l_Lake_configField___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__14_value),((lean_object*)&l_Lake_configField___closed__16_value)}};
static const lean_object* l_Lake_configField___closed__17 = (const lean_object*)&l_Lake_configField___closed__17_value;
static const lean_ctor_object l_Lake_configField___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__6_value),((lean_object*)&l_Lake_configField___closed__17_value)}};
static const lean_object* l_Lake_configField___closed__18 = (const lean_object*)&l_Lake_configField___closed__18_value;
static const lean_ctor_object l_Lake_configField___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__11_value),((lean_object*)&l_Lake_configField___closed__18_value)}};
static const lean_object* l_Lake_configField___closed__19 = (const lean_object*)&l_Lake_configField___closed__19_value;
static const lean_ctor_object l_Lake_configField___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__9_value),((lean_object*)&l_Lake_configField___closed__19_value)}};
static const lean_object* l_Lake_configField___closed__20 = (const lean_object*)&l_Lake_configField___closed__20_value;
static const lean_string_object l_Lake_configField___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_configField___closed__21 = (const lean_object*)&l_Lake_configField___closed__21_value;
static const lean_string_object l_Lake_configField___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lake_configField___closed__22 = (const lean_object*)&l_Lake_configField___closed__22_value;
static const lean_ctor_object l_Lake_configField___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_configField___closed__22_value)}};
static const lean_object* l_Lake_configField___closed__23 = (const lean_object*)&l_Lake_configField___closed__23_value;
static const lean_ctor_object l_Lake_configField___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lake_configField___closed__14_value),((lean_object*)&l_Lake_configField___closed__21_value),((lean_object*)&l_Lake_configField___closed__23_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_configField___closed__24 = (const lean_object*)&l_Lake_configField___closed__24_value;
static const lean_ctor_object l_Lake_configField___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__20_value),((lean_object*)&l_Lake_configField___closed__24_value)}};
static const lean_object* l_Lake_configField___closed__25 = (const lean_object*)&l_Lake_configField___closed__25_value;
static const lean_ctor_object l_Lake_configField___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__6_value),((lean_object*)&l_Lake_configField___closed__25_value)}};
static const lean_object* l_Lake_configField___closed__26 = (const lean_object*)&l_Lake_configField___closed__26_value;
static const lean_string_object l_Lake_configField___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lake_configField___closed__27 = (const lean_object*)&l_Lake_configField___closed__27_value;
static const lean_ctor_object l_Lake_configField___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__27_value),LEAN_SCALAR_PTR_LITERAL(79, 160, 221, 255, 50, 155, 99, 177)}};
static const lean_object* l_Lake_configField___closed__28 = (const lean_object*)&l_Lake_configField___closed__28_value;
static const lean_ctor_object l_Lake_configField___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configField___closed__28_value)}};
static const lean_object* l_Lake_configField___closed__29 = (const lean_object*)&l_Lake_configField___closed__29_value;
static const lean_ctor_object l_Lake_configField___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__26_value),((lean_object*)&l_Lake_configField___closed__29_value)}};
static const lean_object* l_Lake_configField___closed__30 = (const lean_object*)&l_Lake_configField___closed__30_value;
static const lean_string_object l_Lake_configField___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_configField___closed__31 = (const lean_object*)&l_Lake_configField___closed__31_value;
static const lean_ctor_object l_Lake_configField___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_configField___closed__31_value)}};
static const lean_object* l_Lake_configField___closed__32 = (const lean_object*)&l_Lake_configField___closed__32_value;
static const lean_string_object l_Lake_configField___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_configField___closed__33 = (const lean_object*)&l_Lake_configField___closed__33_value;
static const lean_ctor_object l_Lake_configField___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__33_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_configField___closed__34 = (const lean_object*)&l_Lake_configField___closed__34_value;
static const lean_ctor_object l_Lake_configField___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_configField___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_configField___closed__35 = (const lean_object*)&l_Lake_configField___closed__35_value;
static const lean_ctor_object l_Lake_configField___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__32_value),((lean_object*)&l_Lake_configField___closed__35_value)}};
static const lean_object* l_Lake_configField___closed__36 = (const lean_object*)&l_Lake_configField___closed__36_value;
static const lean_ctor_object l_Lake_configField___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__11_value),((lean_object*)&l_Lake_configField___closed__36_value)}};
static const lean_object* l_Lake_configField___closed__37 = (const lean_object*)&l_Lake_configField___closed__37_value;
static const lean_ctor_object l_Lake_configField___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configField___closed__30_value),((lean_object*)&l_Lake_configField___closed__37_value)}};
static const lean_object* l_Lake_configField___closed__38 = (const lean_object*)&l_Lake_configField___closed__38_value;
static const lean_ctor_object l_Lake_configField___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_configField___closed__0_value),((lean_object*)&l_Lake_configField___closed__2_value),((lean_object*)&l_Lake_configField___closed__38_value)}};
static const lean_object* l_Lake_configField___closed__39 = (const lean_object*)&l_Lake_configField___closed__39_value;
LEAN_EXPORT const lean_object* l_Lake_configField = (const lean_object*)&l_Lake_configField___closed__39_value;
static const lean_string_object l_Lake_configDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configDecl"};
static const lean_object* l_Lake_configDecl___closed__0 = (const lean_object*)&l_Lake_configDecl___closed__0_value;
static const lean_ctor_object l_Lake_configDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_configDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 67, 129, 86, 42, 160, 126, 252)}};
static const lean_object* l_Lake_configDecl___closed__1 = (const lean_object*)&l_Lake_configDecl___closed__1_value;
static const lean_string_object l_Lake_configDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_configDecl___closed__2 = (const lean_object*)&l_Lake_configDecl___closed__2_value;
static const lean_ctor_object l_Lake_configDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 135, 0, 93, 130, 217, 220, 132)}};
static const lean_object* l_Lake_configDecl___closed__3 = (const lean_object*)&l_Lake_configDecl___closed__3_value;
static const lean_ctor_object l_Lake_configDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__3_value)}};
static const lean_object* l_Lake_configDecl___closed__4 = (const lean_object*)&l_Lake_configDecl___closed__4_value;
static const lean_string_object l_Lake_configDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "configuration "};
static const lean_object* l_Lake_configDecl___closed__5 = (const lean_object*)&l_Lake_configDecl___closed__5_value;
static const lean_ctor_object l_Lake_configDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__5_value)}};
static const lean_object* l_Lake_configDecl___closed__6 = (const lean_object*)&l_Lake_configDecl___closed__6_value;
static const lean_ctor_object l_Lake_configDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__6_value)}};
static const lean_object* l_Lake_configDecl___closed__7 = (const lean_object*)&l_Lake_configDecl___closed__7_value;
static const lean_string_object l_Lake_configDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_configDecl___closed__8 = (const lean_object*)&l_Lake_configDecl___closed__8_value;
static const lean_ctor_object l_Lake_configDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(210, 155, 24, 168, 139, 44, 164, 47)}};
static const lean_object* l_Lake_configDecl___closed__9 = (const lean_object*)&l_Lake_configDecl___closed__9_value;
static const lean_ctor_object l_Lake_configDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__9_value)}};
static const lean_object* l_Lake_configDecl___closed__10 = (const lean_object*)&l_Lake_configDecl___closed__10_value;
static const lean_ctor_object l_Lake_configDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__7_value),((lean_object*)&l_Lake_configDecl___closed__10_value)}};
static const lean_object* l_Lake_configDecl___closed__11 = (const lean_object*)&l_Lake_configDecl___closed__11_value;
static const lean_string_object l_Lake_configDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l_Lake_configDecl___closed__12 = (const lean_object*)&l_Lake_configDecl___closed__12_value;
static const lean_ctor_object l_Lake_configDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__12_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l_Lake_configDecl___closed__13 = (const lean_object*)&l_Lake_configDecl___closed__13_value;
static const lean_string_object l_Lake_configDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lake_configDecl___closed__14 = (const lean_object*)&l_Lake_configDecl___closed__14_value;
static const lean_ctor_object l_Lake_configDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__14_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lake_configDecl___closed__15 = (const lean_object*)&l_Lake_configDecl___closed__15_value;
static const lean_string_object l_Lake_configDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lake_configDecl___closed__16 = (const lean_object*)&l_Lake_configDecl___closed__16_value;
static const lean_ctor_object l_Lake_configDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__16_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lake_configDecl___closed__17 = (const lean_object*)&l_Lake_configDecl___closed__17_value;
static const lean_ctor_object l_Lake_configDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__17_value)}};
static const lean_object* l_Lake_configDecl___closed__18 = (const lean_object*)&l_Lake_configDecl___closed__18_value;
static const lean_string_object l_Lake_configDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bracketedBinder"};
static const lean_object* l_Lake_configDecl___closed__19 = (const lean_object*)&l_Lake_configDecl___closed__19_value;
static const lean_ctor_object l_Lake_configDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__19_value),LEAN_SCALAR_PTR_LITERAL(126, 188, 9, 177, 18, 110, 216, 30)}};
static const lean_object* l_Lake_configDecl___closed__20 = (const lean_object*)&l_Lake_configDecl___closed__20_value;
static const lean_ctor_object l_Lake_configDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__20_value)}};
static const lean_object* l_Lake_configDecl___closed__21 = (const lean_object*)&l_Lake_configDecl___closed__21_value;
static const lean_ctor_object l_Lake_configDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__18_value),((lean_object*)&l_Lake_configDecl___closed__21_value)}};
static const lean_object* l_Lake_configDecl___closed__22 = (const lean_object*)&l_Lake_configDecl___closed__22_value;
static const lean_ctor_object l_Lake_configDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__15_value),((lean_object*)&l_Lake_configDecl___closed__22_value)}};
static const lean_object* l_Lake_configDecl___closed__23 = (const lean_object*)&l_Lake_configDecl___closed__23_value;
static const lean_string_object l_Lake_configDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_configDecl___closed__24 = (const lean_object*)&l_Lake_configDecl___closed__24_value;
static const lean_string_object l_Lake_configDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_configDecl___closed__25 = (const lean_object*)&l_Lake_configDecl___closed__25_value;
static const lean_string_object l_Lake_configDecl___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_configDecl___closed__26 = (const lean_object*)&l_Lake_configDecl___closed__26_value;
static const lean_string_object l_Lake_configDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "optType"};
static const lean_object* l_Lake_configDecl___closed__27 = (const lean_object*)&l_Lake_configDecl___closed__27_value;
static const lean_ctor_object l_Lake_configDecl___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_configDecl___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__28_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_configDecl___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__28_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_configDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__28_value_aux_2),((lean_object*)&l_Lake_configDecl___closed__27_value),LEAN_SCALAR_PTR_LITERAL(230, 186, 93, 163, 90, 7, 206, 225)}};
static const lean_object* l_Lake_configDecl___closed__28 = (const lean_object*)&l_Lake_configDecl___closed__28_value;
static const lean_ctor_object l_Lake_configDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__28_value)}};
static const lean_object* l_Lake_configDecl___closed__29 = (const lean_object*)&l_Lake_configDecl___closed__29_value;
static const lean_ctor_object l_Lake_configDecl___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__23_value),((lean_object*)&l_Lake_configDecl___closed__29_value)}};
static const lean_object* l_Lake_configDecl___closed__30 = (const lean_object*)&l_Lake_configDecl___closed__30_value;
static const lean_string_object l_Lake_configDecl___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_configDecl___closed__31 = (const lean_object*)&l_Lake_configDecl___closed__31_value;
static const lean_string_object l_Lake_configDecl___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extends"};
static const lean_object* l_Lake_configDecl___closed__32 = (const lean_object*)&l_Lake_configDecl___closed__32_value;
static const lean_ctor_object l_Lake_configDecl___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_configDecl___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__33_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_configDecl___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__33_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_configDecl___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__33_value_aux_2),((lean_object*)&l_Lake_configDecl___closed__32_value),LEAN_SCALAR_PTR_LITERAL(231, 24, 97, 144, 91, 250, 92, 29)}};
static const lean_object* l_Lake_configDecl___closed__33 = (const lean_object*)&l_Lake_configDecl___closed__33_value;
static const lean_ctor_object l_Lake_configDecl___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__33_value)}};
static const lean_object* l_Lake_configDecl___closed__34 = (const lean_object*)&l_Lake_configDecl___closed__34_value;
static const lean_ctor_object l_Lake_configDecl___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__11_value),((lean_object*)&l_Lake_configDecl___closed__34_value)}};
static const lean_object* l_Lake_configDecl___closed__35 = (const lean_object*)&l_Lake_configDecl___closed__35_value;
static const lean_ctor_object l_Lake_configDecl___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__30_value),((lean_object*)&l_Lake_configDecl___closed__35_value)}};
static const lean_object* l_Lake_configDecl___closed__36 = (const lean_object*)&l_Lake_configDecl___closed__36_value;
static const lean_ctor_object l_Lake_configDecl___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__13_value),((lean_object*)&l_Lake_configDecl___closed__36_value)}};
static const lean_object* l_Lake_configDecl___closed__37 = (const lean_object*)&l_Lake_configDecl___closed__37_value;
static const lean_ctor_object l_Lake_configDecl___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__11_value),((lean_object*)&l_Lake_configDecl___closed__37_value)}};
static const lean_object* l_Lake_configDecl___closed__38 = (const lean_object*)&l_Lake_configDecl___closed__38_value;
static const lean_string_object l_Lake_configDecl___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lake_configDecl___closed__39 = (const lean_object*)&l_Lake_configDecl___closed__39_value;
static const lean_ctor_object l_Lake_configDecl___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__39_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lake_configDecl___closed__40 = (const lean_object*)&l_Lake_configDecl___closed__40_value;
static const lean_string_object l_Lake_configDecl___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lake_configDecl___closed__41 = (const lean_object*)&l_Lake_configDecl___closed__41_value;
static const lean_ctor_object l_Lake_configDecl___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__41_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lake_configDecl___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__42_value_aux_0),((lean_object*)&l_Lake_configField___closed__31_value),LEAN_SCALAR_PTR_LITERAL(243, 64, 60, 42, 244, 245, 53, 52)}};
static const lean_object* l_Lake_configDecl___closed__42 = (const lean_object*)&l_Lake_configDecl___closed__42_value;
static const lean_ctor_object l_Lake_configDecl___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_configField___closed__31_value),((lean_object*)&l_Lake_configDecl___closed__42_value),((lean_object*)&l_Lake_configField___closed__32_value)}};
static const lean_object* l_Lake_configDecl___closed__43 = (const lean_object*)&l_Lake_configDecl___closed__43_value;
static const lean_string_object l_Lake_configDecl___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " where "};
static const lean_object* l_Lake_configDecl___closed__44 = (const lean_object*)&l_Lake_configDecl___closed__44_value;
static const lean_ctor_object l_Lake_configDecl___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__41_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lake_configDecl___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__45_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__44_value),LEAN_SCALAR_PTR_LITERAL(197, 177, 143, 70, 3, 238, 86, 51)}};
static const lean_object* l_Lake_configDecl___closed__45 = (const lean_object*)&l_Lake_configDecl___closed__45_value;
static const lean_ctor_object l_Lake_configDecl___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__44_value)}};
static const lean_object* l_Lake_configDecl___closed__46 = (const lean_object*)&l_Lake_configDecl___closed__46_value;
static const lean_ctor_object l_Lake_configDecl___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__44_value),((lean_object*)&l_Lake_configDecl___closed__45_value),((lean_object*)&l_Lake_configDecl___closed__46_value)}};
static const lean_object* l_Lake_configDecl___closed__47 = (const lean_object*)&l_Lake_configDecl___closed__47_value;
static const lean_ctor_object l_Lake_configDecl___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__40_value),((lean_object*)&l_Lake_configDecl___closed__43_value),((lean_object*)&l_Lake_configDecl___closed__47_value)}};
static const lean_object* l_Lake_configDecl___closed__48 = (const lean_object*)&l_Lake_configDecl___closed__48_value;
static const lean_string_object l_Lake_configDecl___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structCtor"};
static const lean_object* l_Lake_configDecl___closed__49 = (const lean_object*)&l_Lake_configDecl___closed__49_value;
static const lean_ctor_object l_Lake_configDecl___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_configDecl___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__50_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_configDecl___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__50_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_configDecl___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__50_value_aux_2),((lean_object*)&l_Lake_configDecl___closed__49_value),LEAN_SCALAR_PTR_LITERAL(56, 67, 52, 180, 140, 36, 149, 125)}};
static const lean_object* l_Lake_configDecl___closed__50 = (const lean_object*)&l_Lake_configDecl___closed__50_value;
static const lean_ctor_object l_Lake_configDecl___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__50_value)}};
static const lean_object* l_Lake_configDecl___closed__51 = (const lean_object*)&l_Lake_configDecl___closed__51_value;
static const lean_ctor_object l_Lake_configDecl___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__11_value),((lean_object*)&l_Lake_configDecl___closed__51_value)}};
static const lean_object* l_Lake_configDecl___closed__52 = (const lean_object*)&l_Lake_configDecl___closed__52_value;
static const lean_ctor_object l_Lake_configDecl___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__48_value),((lean_object*)&l_Lake_configDecl___closed__52_value)}};
static const lean_object* l_Lake_configDecl___closed__53 = (const lean_object*)&l_Lake_configDecl___closed__53_value;
static const lean_string_object l_Lake_configDecl___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "manyIndent"};
static const lean_object* l_Lake_configDecl___closed__54 = (const lean_object*)&l_Lake_configDecl___closed__54_value;
static const lean_ctor_object l_Lake_configDecl___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(151, 35, 49, 198, 227, 245, 222, 169)}};
static const lean_object* l_Lake_configDecl___closed__55 = (const lean_object*)&l_Lake_configDecl___closed__55_value;
static const lean_string_object l_Lake_configDecl___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lake_configDecl___closed__56 = (const lean_object*)&l_Lake_configDecl___closed__56_value;
static const lean_ctor_object l_Lake_configDecl___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__56_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lake_configDecl___closed__57 = (const lean_object*)&l_Lake_configDecl___closed__57_value;
static const lean_ctor_object l_Lake_configDecl___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__57_value)}};
static const lean_object* l_Lake_configDecl___closed__58 = (const lean_object*)&l_Lake_configDecl___closed__58_value;
static const lean_string_object l_Lake_configDecl___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lake_configDecl___closed__59 = (const lean_object*)&l_Lake_configDecl___closed__59_value;
static const lean_ctor_object l_Lake_configDecl___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__59_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lake_configDecl___closed__60 = (const lean_object*)&l_Lake_configDecl___closed__60_value;
static const lean_ctor_object l_Lake_configDecl___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__60_value)}};
static const lean_object* l_Lake_configDecl___closed__61 = (const lean_object*)&l_Lake_configDecl___closed__61_value;
static const lean_ctor_object l_Lake_configDecl___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__58_value),((lean_object*)&l_Lake_configDecl___closed__61_value)}};
static const lean_object* l_Lake_configDecl___closed__62 = (const lean_object*)&l_Lake_configDecl___closed__62_value;
static const lean_string_object l_Lake_configDecl___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l_Lake_configDecl___closed__63 = (const lean_object*)&l_Lake_configDecl___closed__63_value;
static const lean_ctor_object l_Lake_configDecl___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__63_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l_Lake_configDecl___closed__64 = (const lean_object*)&l_Lake_configDecl___closed__64_value;
static const lean_ctor_object l_Lake_configDecl___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__64_value),((lean_object*)&l_Lake_configField___closed__39_value)}};
static const lean_object* l_Lake_configDecl___closed__65 = (const lean_object*)&l_Lake_configDecl___closed__65_value;
static const lean_ctor_object l_Lake_configDecl___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__62_value),((lean_object*)&l_Lake_configDecl___closed__65_value)}};
static const lean_object* l_Lake_configDecl___closed__66 = (const lean_object*)&l_Lake_configDecl___closed__66_value;
static const lean_ctor_object l_Lake_configDecl___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__55_value),((lean_object*)&l_Lake_configDecl___closed__66_value)}};
static const lean_object* l_Lake_configDecl___closed__67 = (const lean_object*)&l_Lake_configDecl___closed__67_value;
static const lean_ctor_object l_Lake_configDecl___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__53_value),((lean_object*)&l_Lake_configDecl___closed__67_value)}};
static const lean_object* l_Lake_configDecl___closed__68 = (const lean_object*)&l_Lake_configDecl___closed__68_value;
static const lean_ctor_object l_Lake_configDecl___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configField___closed__11_value),((lean_object*)&l_Lake_configDecl___closed__68_value)}};
static const lean_object* l_Lake_configDecl___closed__69 = (const lean_object*)&l_Lake_configDecl___closed__69_value;
static const lean_ctor_object l_Lake_configDecl___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__38_value),((lean_object*)&l_Lake_configDecl___closed__69_value)}};
static const lean_object* l_Lake_configDecl___closed__70 = (const lean_object*)&l_Lake_configDecl___closed__70_value;
static const lean_string_object l_Lake_configDecl___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optDeriving"};
static const lean_object* l_Lake_configDecl___closed__71 = (const lean_object*)&l_Lake_configDecl___closed__71_value;
static const lean_ctor_object l_Lake_configDecl___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_configDecl___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__72_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_configDecl___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__72_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_configDecl___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__72_value_aux_2),((lean_object*)&l_Lake_configDecl___closed__71_value),LEAN_SCALAR_PTR_LITERAL(215, 163, 253, 206, 79, 89, 101, 240)}};
static const lean_object* l_Lake_configDecl___closed__72 = (const lean_object*)&l_Lake_configDecl___closed__72_value;
static const lean_ctor_object l_Lake_configDecl___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__72_value)}};
static const lean_object* l_Lake_configDecl___closed__73 = (const lean_object*)&l_Lake_configDecl___closed__73_value;
static const lean_ctor_object l_Lake_configDecl___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_configField___closed__4_value),((lean_object*)&l_Lake_configDecl___closed__70_value),((lean_object*)&l_Lake_configDecl___closed__73_value)}};
static const lean_object* l_Lake_configDecl___closed__74 = (const lean_object*)&l_Lake_configDecl___closed__74_value;
static const lean_ctor_object l_Lake_configDecl___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_configDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__74_value)}};
static const lean_object* l_Lake_configDecl___closed__75 = (const lean_object*)&l_Lake_configDecl___closed__75_value;
LEAN_EXPORT const lean_object* l_Lake_configDecl = (const lean_object*)&l_Lake_configDecl___closed__75_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_fields"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "instConfigFields"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instConfigInfo"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instEmptyCollection"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instConfigField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ConfigField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(247, 156, 204, 47, 51, 77, 87, 91)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 228, 204, 215, 72, 103, 209, 63)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__8_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|>."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(234, 36, 132, 139, 128, 248, 8, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "realName"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32_value),LEAN_SCALAR_PTR_LITERAL(144, 209, 47, 186, 198, 69, 114, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 207, 191, 201, 123, 75, 165)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__38_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__39_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ConfigFieldInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43_value),LEAN_SCALAR_PTR_LITERAL(219, 5, 143, 119, 172, 22, 154, 14)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43_value),LEAN_SCALAR_PTR_LITERAL(151, 104, 212, 31, 149, 64, 64, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__47_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__46_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__48_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__49_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__47_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__49_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__52_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__52_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value_aux_2),((lean_object*)&l_Lake_configDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "instConfigParent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__38_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ConfigParent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 44, 166, 143, 34, 174, 28, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(100, 115, 34, 99, 165, 32, 152, 125)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ConfigFields.fields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__17_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ConfigFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 196, 194, 188, 85, 136, 250)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20_value),LEAN_SCALAR_PTR_LITERAL(51, 161, 135, 158, 114, 114, 169, 2)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23_value),LEAN_SCALAR_PTR_LITERAL(14, 193, 30, 208, 65, 149, 209, 94)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigProj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31_value),LEAN_SCALAR_PTR_LITERAL(20, 253, 220, 72, 95, 155, 159, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31_value),LEAN_SCALAR_PTR_LITERAL(80, 193, 48, 218, 209, 214, 51, 12)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__34_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__36_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__35_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__37_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41_value),LEAN_SCALAR_PTR_LITERAL(149, 195, 233, 5, 41, 184, 182, 9)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MonadState"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__44_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__44_value),LEAN_SCALAR_PTR_LITERAL(133, 87, 22, 123, 153, 115, 76, 72)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41_value),LEAN_SCALAR_PTR_LITERAL(171, 90, 209, 238, 200, 105, 147, 59)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53_value),LEAN_SCALAR_PTR_LITERAL(251, 234, 199, 196, 105, 204, 214, 2)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "MonadStateOf"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__56 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__56_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__56_value),LEAN_SCALAR_PTR_LITERAL(190, 161, 118, 134, 19, 241, 250, 34)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53_value),LEAN_SCALAR_PTR_LITERAL(18, 82, 123, 92, 236, 217, 106, 211)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__58 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__58_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60_value),LEAN_SCALAR_PTR_LITERAL(228, 28, 19, 111, 76, 58, 44, 203)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "modify"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64_value),LEAN_SCALAR_PTR_LITERAL(28, 15, 159, 80, 159, 14, 30, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__67 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__67_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__67_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkDefault"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72_value),LEAN_SCALAR_PTR_LITERAL(198, 16, 75, 188, 15, 169, 2, 241)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "UnhygienicMain"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__0_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 242, 144, 140, 56, 85, 78)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__2 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__2_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "empty"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__3 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4_value_aux_0),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 156, 216, 135, 178, 199, 82, 94)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5;
static const lean_array_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Array.empty"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__9 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__9_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "EmptyCollection"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18_value),LEAN_SCALAR_PTR_LITERAL(236, 209, 69, 209, 212, 29, 83, 196)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__21 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__21_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20_value)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__22 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__22_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__23 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__23_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__21_value),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__23_value)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__25 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__25_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__25_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__27 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__27_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__27_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigInfo"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29_value),LEAN_SCALAR_PTR_LITERAL(100, 26, 82, 225, 106, 6, 63, 188)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__32 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__32_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value_aux_2),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__32_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20_value),LEAN_SCALAR_PTR_LITERAL(186, 249, 167, 146, 96, 188, 95, 76)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arity"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37_value),LEAN_SCALAR_PTR_LITERAL(251, 206, 108, 50, 170, 163, 91, 135)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 196, 194, 188, 85, 136, 250)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19_value),LEAN_SCALAR_PTR_LITERAL(106, 121, 165, 74, 234, 116, 106, 233)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__50 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__50_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__49_value)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__51 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__51_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__51_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__52 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__52_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__50_value),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__52_value)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "ill-formed configuration field declaration"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structSimpleBinder"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__1 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__1_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value_aux_2),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 230, 214, 182, 254, 52, 213, 225)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binderDefault"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a default value"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "expected a least one field name"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value_aux_2),((lean_object*)&l_Lake_configField___closed__27_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "to"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structParent"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__0_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value_aux_2),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 41, 245, 205, 163, 229, 236, 195)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term∅"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__2 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 213, 176, 183, 122, 236, 171, 252)}};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∅"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4_value;
static lean_once_cell_t l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ill-formed parent"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6_value;
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unsupported parent syntax"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_expandConfigDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed configuration declaration"};
static const lean_object* l_Lake_expandConfigDecl___closed__0 = (const lean_object*)&l_Lake_expandConfigDecl___closed__0_value;
static const lean_string_object l_Lake_expandConfigDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structFields"};
static const lean_object* l_Lake_expandConfigDecl___closed__1 = (const lean_object*)&l_Lake_expandConfigDecl___closed__1_value;
static const lean_ctor_object l_Lake_expandConfigDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__2_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__2_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__2_value_aux_2),((lean_object*)&l_Lake_expandConfigDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 20, 124, 55, 90, 140, 156, 83)}};
static const lean_object* l_Lake_expandConfigDecl___closed__2 = (const lean_object*)&l_Lake_expandConfigDecl___closed__2_value;
static lean_once_cell_t l_Lake_expandConfigDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_expandConfigDecl___closed__3;
static const lean_string_object l_Lake_expandConfigDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l_Lake_expandConfigDecl___closed__4 = (const lean_object*)&l_Lake_expandConfigDecl___closed__4_value;
static const lean_ctor_object l_Lake_expandConfigDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__5_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__5_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__5_value_aux_2),((lean_object*)&l_Lake_expandConfigDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l_Lake_expandConfigDecl___closed__5 = (const lean_object*)&l_Lake_expandConfigDecl___closed__5_value;
static const lean_string_object l_Lake_expandConfigDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "structureTk"};
static const lean_object* l_Lake_expandConfigDecl___closed__6 = (const lean_object*)&l_Lake_expandConfigDecl___closed__6_value;
static const lean_ctor_object l_Lake_expandConfigDecl___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configDecl___closed__24_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__7_value_aux_0),((lean_object*)&l_Lake_configDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__7_value_aux_1),((lean_object*)&l_Lake_configDecl___closed__31_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_expandConfigDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandConfigDecl___closed__7_value_aux_2),((lean_object*)&l_Lake_expandConfigDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(132, 164, 13, 167, 248, 219, 132, 242)}};
static const lean_object* l_Lake_expandConfigDecl___closed__7 = (const lean_object*)&l_Lake_expandConfigDecl___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0(void){
_start:
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = 0;
v___x_277_ = lean_box(0);
v___x_278_ = l_Lean_SourceInfo_fromRef(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Array_mkArray0(lean_box(0));
return v___x_288_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_290_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_291_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0(lean_object* v_stx_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_295_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2));
v___x_296_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6);
v___x_297_ = l_Lean_Syntax_node2(v___x_294_, v___x_295_, v_stx_293_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(lean_object* v_____do__lift_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = 0;
v___x_304_ = l_Lean_SourceInfo_fromRef(v_____do__lift_300_, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___y_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0___boxed(lean_object* v_____do__lift_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_____do__lift_306_, v___y_307_, v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v_____do__lift_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0));
v___x_313_ = l_Lean_Name_str___override(v_x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0));
v___x_317_ = l_Lean_Name_str___override(v_x_315_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0));
v___x_321_ = l_Lean_Name_str___override(v_x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4___closed__0));
v___x_325_ = l_Lean_Name_str___override(v_x_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(lean_object* v_a_332_, lean_object* v___x_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_bs_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_lt(v_i_335_, v_sz_334_);
if (v___x_337_ == 0)
{
lean_dec(v___x_333_);
lean_dec(v_a_332_);
return v_bs_336_;
}
else
{
lean_object* v_v_338_; lean_object* v___x_339_; lean_object* v_bs_x27_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; 
v_v_338_ = lean_array_uget(v_bs_336_, v_i_335_);
v___x_339_ = lean_unsigned_to_nat(0u);
v_bs_x27_340_ = lean_array_uset(v_bs_336_, v_i_335_, v___x_339_);
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1));
v___x_342_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2));
lean_inc_n(v___x_333_, 2);
lean_inc_n(v_a_332_, 2);
v___x_343_ = l_Lean_Syntax_node2(v_a_332_, v___x_342_, v_v_338_, v___x_333_);
v___x_344_ = l_Lean_Syntax_node2(v_a_332_, v___x_341_, v___x_343_, v___x_333_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_335_, v___x_345_);
v___x_347_ = lean_array_uset(v_bs_x27_340_, v_i_335_, v___x_344_);
v_i_335_ = v___x_346_;
v_bs_336_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___boxed(lean_object* v_a_349_, lean_object* v___x_350_, lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_bs_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_355_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_349_, v___x_350_, v_sz_boxed_354_, v_i_boxed_355_, v_bs_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(uint8_t v___x_357_, lean_object* v_____do__lift_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = l_Lean_SourceInfo_fromRef(v_____do__lift_358_, v___x_357_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1___boxed(lean_object* v___x_363_, lean_object* v_____do__lift_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v___x_80827__boxed_367_; lean_object* v_res_368_; 
v___x_80827__boxed_367_ = lean_unbox(v___x_363_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_80827__boxed_367_, v_____do__lift_364_, v___y_365_, v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v_____do__lift_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(lean_object* v_structId_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_372_ = l_Lean_TSyntax_getId(v_structId_370_);
v___x_373_ = l_Lean_Name_append(v___x_372_, v_x_371_);
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___closed__0));
v___x_375_ = l_Lean_Name_str___override(v___x_373_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___boxed(lean_object* v_structId_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_376_, v_x_377_);
lean_dec(v_structId_376_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_386_ = l_String_toRawSubstring_x27(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22));
v___x_414_ = l_String_toRawSubstring_x27(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28));
v___x_422_ = l_String_toRawSubstring_x27(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35));
v___x_433_ = l_String_toRawSubstring_x27(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40));
v___x_442_ = l_Lean_mkCIdent(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_446_ = l_String_toRawSubstring_x27(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(lean_object* v_structTy_477_, lean_object* v_type_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v_vis_x3f_481_, lean_object* v_structId_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_489_ == 0)
{
lean_object* v_cmds_490_; lean_object* v_fields_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_701_; 
v_cmds_490_ = lean_ctor_get(v_b_486_, 0);
v_fields_491_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_701_ == 0)
{
v___x_493_ = v_b_486_;
v_isShared_494_ = v_isSharedCheck_701_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_fields_491_);
lean_inc(v_cmds_490_);
lean_dec(v_b_486_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_701_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_654_; uint8_t v___x_685_; 
v___x_495_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
v___x_496_ = l_Lean_TSyntax_getId(v___x_495_);
lean_inc(v___x_496_);
lean_inc(v___x_495_);
v___x_497_ = l_Lake_Name_quoteFrom(v___x_495_, v___x_496_, v___x_489_);
v___x_685_ = l_Lean_Name_hasMacroScopes(v___x_496_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_482_, v___x_496_);
v___y_654_ = v___x_686_;
goto v___jp_653_;
}
else
{
lean_object* v_view_687_; lean_object* v_name_688_; lean_object* v_imported_689_; lean_object* v_ctx_690_; lean_object* v_scopes_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
v_view_687_ = l_Lean_extractMacroScopes(v___x_496_);
v_name_688_ = lean_ctor_get(v_view_687_, 0);
v_imported_689_ = lean_ctor_get(v_view_687_, 1);
v_ctx_690_ = lean_ctor_get(v_view_687_, 2);
v_scopes_691_ = lean_ctor_get(v_view_687_, 3);
v_isSharedCheck_700_ = !lean_is_exclusive(v_view_687_);
if (v_isSharedCheck_700_ == 0)
{
v___x_693_ = v_view_687_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_scopes_691_);
lean_inc(v_ctx_690_);
lean_inc(v_imported_689_);
lean_inc(v_name_688_);
lean_dec(v_view_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_482_, v_name_688_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_imported_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ctx_690_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_scopes_691_);
v___x_697_ = v_reuseFailAlloc_699_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_MacroScopesView_review(v___x_697_);
v___y_654_ = v___x_698_;
goto v___jp_653_;
}
}
}
v___jp_498_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_ref_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_inc_ref(v___y_507_);
v___x_517_ = l_Array_append___redArg(v___y_507_, v___y_516_);
lean_dec_ref(v___y_516_);
lean_inc_n(v___y_500_, 4);
lean_inc_n(v___y_508_, 18);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v___y_508_);
lean_ctor_set(v___x_518_, 1, v___y_500_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_inc_n(v___y_509_, 11);
lean_inc(v___y_514_);
v___x_519_ = l_Lean_Syntax_node7(v___y_508_, v___y_514_, v___y_509_, v___y_509_, v___x_518_, v___y_509_, v___y_509_, v___y_509_, v___y_509_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_504_, 4);
lean_inc_ref_n(v___y_513_, 9);
lean_inc_ref_n(v___y_506_, 9);
v___x_521_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___y_504_, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_524_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_523_);
v___x_525_ = l_Lean_Syntax_node1(v___y_508_, v___x_524_, v___y_509_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_508_);
lean_ctor_set(v___x_526_, 1, v___x_520_);
v___x_527_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_528_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___y_504_, v___x_527_);
v___x_529_ = l_Lean_Syntax_node2(v___y_508_, v___x_528_, v___y_499_, v___y_509_);
v___x_530_ = l_Lean_Syntax_node1(v___y_508_, v___y_500_, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_532_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___y_504_, v___x_531_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_534_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_508_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_538_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_537_);
v___x_539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_512_, 2);
lean_inc_n(v___y_515_, 2);
v___x_541_ = l_Lean_addMacroScope(v___y_515_, v___x_540_, v___y_512_);
v___x_542_ = lean_box(0);
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_544_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_544_, 0, v___y_508_);
lean_ctor_set(v___x_544_, 1, v___x_539_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
lean_ctor_set(v___x_544_, 3, v___x_543_);
lean_inc(v_type_478_);
lean_inc(v___x_497_);
lean_inc(v_structTy_477_);
v___x_545_ = l_Lean_Syntax_node3(v___y_508_, v___y_500_, v_structTy_477_, v___x_497_, v_type_478_);
v___x_546_ = l_Lean_Syntax_node2(v___y_508_, v___x_538_, v___x_544_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___y_508_, v___x_534_, v___x_536_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node2(v___y_508_, v___x_532_, v___y_509_, v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_550_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___y_504_, v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v___y_508_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_554_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_508_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
lean_inc(v___x_479_);
v___x_557_ = l_Lean_Syntax_node1(v___y_508_, v___y_500_, v___x_479_);
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_508_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Syntax_node3(v___y_508_, v___x_554_, v___x_556_, v___x_557_, v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_563_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_561_, v___x_562_);
v___x_564_ = l_Lean_Syntax_node2(v___y_508_, v___x_563_, v___y_509_, v___y_509_);
v_ref_565_ = l_Lean_replaceRef(v_fields_491_, v___y_503_);
lean_inc(v_ref_565_);
lean_inc(v___y_502_);
lean_inc(v___y_511_);
lean_inc(v___y_501_);
v___x_566_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_566_, 0, v___y_501_);
lean_ctor_set(v___x_566_, 1, v___y_515_);
lean_ctor_set(v___x_566_, 2, v___y_512_);
lean_ctor_set(v___x_566_, 3, v___y_511_);
lean_ctor_set(v___x_566_, 4, v___y_502_);
lean_ctor_set(v___x_566_, 5, v_ref_565_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_489_, v_ref_565_, v___x_566_, v___y_505_);
lean_dec_ref(v___x_566_);
lean_dec(v_ref_565_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_n(v_a_568_, 30);
v_a_569_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_a_569_);
lean_dec_ref(v___x_567_);
lean_inc(v___y_509_);
lean_inc_n(v___y_508_, 2);
v___x_570_ = l_Lean_Syntax_node4(v___y_508_, v___x_550_, v___x_552_, v___x_560_, v___x_564_, v___y_509_);
v___x_571_ = l_Lean_Syntax_node6(v___y_508_, v___x_521_, v___x_525_, v___x_526_, v___y_509_, v___x_530_, v___x_548_, v___x_570_);
lean_inc(v___y_510_);
v___x_572_ = l_Lean_Syntax_node2(v___y_508_, v___y_510_, v___x_519_, v___x_571_);
v___x_573_ = lean_array_push(v_cmds_490_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_513_, 7);
lean_inc_ref_n(v___y_506_, 7);
v___x_575_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v_a_568_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_512_, 5);
lean_inc_n(v___y_515_, 5);
v___x_580_ = l_Lean_addMacroScope(v___y_515_, v___x_579_, v___y_512_);
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v_a_568_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_542_);
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_583_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_568_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_inc_ref(v___y_507_);
lean_inc_n(v___y_500_, 7);
v___x_586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_586_, 0, v_a_568_);
lean_ctor_set(v___x_586_, 1, v___y_500_);
lean_ctor_set(v___x_586_, 2, v___y_507_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_588_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_590_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_592_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_591_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_595_ = l_Lean_addMacroScope(v___y_515_, v___x_594_, v___y_512_);
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v_a_568_);
lean_ctor_set(v___x_596_, 1, v___x_593_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_ctor_set(v___x_596_, 3, v___x_542_);
lean_inc_ref_n(v___x_586_, 16);
lean_inc_n(v___x_592_, 2);
v___x_597_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_596_, v___x_586_);
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_599_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_598_);
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_568_);
lean_ctor_set(v___x_600_, 1, v___x_551_);
lean_inc_ref_n(v___x_600_, 2);
lean_inc_n(v___x_599_, 2);
v___x_601_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_586_, v___x_497_);
v___x_602_ = l_Lean_Syntax_node3(v_a_568_, v___y_500_, v___x_586_, v___x_586_, v___x_601_);
lean_inc_n(v___x_590_, 2);
v___x_603_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_597_, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_606_ = l_Lean_addMacroScope(v___y_515_, v___x_605_, v___y_512_);
v___x_607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_607_, 0, v_a_568_);
lean_ctor_set(v___x_607_, 1, v___x_604_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
lean_ctor_set(v___x_607_, 3, v___x_542_);
v___x_608_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_607_, v___x_586_);
lean_inc(v___x_480_);
v___x_609_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_586_, v___x_480_);
v___x_610_ = l_Lean_Syntax_node3(v_a_568_, v___y_500_, v___x_586_, v___x_586_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_608_, v___x_610_);
v___x_612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_614_ = l_Lean_addMacroScope(v___y_515_, v___x_613_, v___y_512_);
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v_a_568_);
lean_ctor_set(v___x_615_, 1, v___x_612_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_ctor_set(v___x_615_, 3, v___x_542_);
v___x_616_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_615_, v___x_586_);
v___x_617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_618_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_586_, v___x_617_);
v___x_619_ = l_Lean_Syntax_node3(v_a_568_, v___y_500_, v___x_586_, v___x_586_, v___x_618_);
v___x_620_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_616_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node6(v_a_568_, v___y_500_, v___x_603_, v___x_586_, v___x_611_, v___x_586_, v___x_620_, v___x_586_);
v___x_622_ = l_Lean_Syntax_node1(v_a_568_, v___x_588_, v___x_621_);
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_624_ = l_Lean_Name_mkStr4(v___y_506_, v___y_513_, v___x_522_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node1(v_a_568_, v___x_624_, v___x_586_);
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v_a_568_);
lean_ctor_set(v___x_626_, 1, v___x_535_);
v___x_627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_629_ = l_Lean_addMacroScope(v___y_515_, v___x_628_, v___y_512_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_631_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_631_, 0, v_a_568_);
lean_ctor_set(v___x_631_, 1, v___x_627_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
lean_ctor_set(v___x_631_, 3, v___x_630_);
v___x_632_ = l_Lean_Syntax_node2(v_a_568_, v___y_500_, v___x_626_, v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_634_, 0, v_a_568_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_Syntax_node6(v_a_568_, v___x_583_, v___x_585_, v___x_586_, v___x_622_, v___x_625_, v___x_632_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node1(v_a_568_, v___y_500_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node4(v_a_568_, v___x_575_, v_fields_491_, v___x_577_, v___x_581_, v___x_636_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_637_);
lean_ctor_set(v___x_493_, 0, v___x_573_);
v___x_639_ = v___x_493_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
size_t v___x_640_; size_t v___x_641_; 
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_484_, v___x_640_);
v_i_484_ = v___x_641_;
v_b_486_ = v___x_639_;
v___y_488_ = v_a_569_;
goto _start;
}
}
else
{
lean_object* v_a_644_; lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v___x_564_);
lean_dec(v___x_560_);
lean_dec_ref(v___x_552_);
lean_dec(v___x_550_);
lean_dec(v___x_548_);
lean_dec(v___x_530_);
lean_dec_ref(v___x_526_);
lean_dec(v___x_525_);
lean_dec(v___x_521_);
lean_dec(v___x_519_);
lean_dec(v___y_509_);
lean_dec(v___y_508_);
lean_dec(v___x_497_);
lean_del_object(v___x_493_);
lean_dec(v_fields_491_);
lean_dec_ref(v_cmds_490_);
lean_dec(v_vis_x3f_481_);
lean_dec(v___x_480_);
lean_dec(v___x_479_);
lean_dec(v_type_478_);
lean_dec(v_structTy_477_);
v_a_644_ = lean_ctor_get(v___x_567_, 0);
v_a_645_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_567_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_inc(v_a_644_);
lean_dec(v___x_567_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_644_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
v___jp_653_:
{
lean_object* v_methods_655_; lean_object* v_quotContext_656_; lean_object* v_currMacroScope_657_; lean_object* v_currRecDepth_658_; lean_object* v_maxRecDepth_659_; lean_object* v_ref_660_; lean_object* v___x_661_; 
v_methods_655_ = lean_ctor_get(v___y_487_, 0);
v_quotContext_656_ = lean_ctor_get(v___y_487_, 1);
v_currMacroScope_657_ = lean_ctor_get(v___y_487_, 2);
v_currRecDepth_658_ = lean_ctor_get(v___y_487_, 3);
v_maxRecDepth_659_ = lean_ctor_get(v___y_487_, 4);
v_ref_660_ = lean_ctor_get(v___y_487_, 5);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_489_, v_ref_660_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_n(v_a_662_, 2);
v_a_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_a_663_);
lean_dec_ref(v___x_661_);
v___x_664_ = l_Lean_mkIdentFrom(v___x_495_, v___y_654_, v___x_489_);
v___x_665_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_666_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_667_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_670_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_671_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_672_, 0, v_a_662_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
if (lean_obj_tag(v_vis_x3f_481_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v_vis_x3f_481_, 0);
lean_inc(v_val_673_);
v___x_674_ = l_Array_mkArray1___redArg(v_val_673_);
v___y_499_ = v___x_664_;
v___y_500_ = v___x_670_;
v___y_501_ = v_methods_655_;
v___y_502_ = v_maxRecDepth_659_;
v___y_503_ = v_ref_660_;
v___y_504_ = v___x_667_;
v___y_505_ = v_a_663_;
v___y_506_ = v___x_665_;
v___y_507_ = v___x_671_;
v___y_508_ = v_a_662_;
v___y_509_ = v___x_672_;
v___y_510_ = v___x_668_;
v___y_511_ = v_currRecDepth_658_;
v___y_512_ = v_currMacroScope_657_;
v___y_513_ = v___x_666_;
v___y_514_ = v___x_669_;
v___y_515_ = v_quotContext_656_;
v___y_516_ = v___x_674_;
goto v___jp_498_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_499_ = v___x_664_;
v___y_500_ = v___x_670_;
v___y_501_ = v_methods_655_;
v___y_502_ = v_maxRecDepth_659_;
v___y_503_ = v_ref_660_;
v___y_504_ = v___x_667_;
v___y_505_ = v_a_663_;
v___y_506_ = v___x_665_;
v___y_507_ = v___x_671_;
v___y_508_ = v_a_662_;
v___y_509_ = v___x_672_;
v___y_510_ = v___x_668_;
v___y_511_ = v_currRecDepth_658_;
v___y_512_ = v_currMacroScope_657_;
v___y_513_ = v___x_666_;
v___y_514_ = v___x_669_;
v___y_515_ = v_quotContext_656_;
v___y_516_ = v___x_675_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___y_654_);
lean_dec(v___x_497_);
lean_del_object(v___x_493_);
lean_dec(v_fields_491_);
lean_dec_ref(v_cmds_490_);
lean_dec(v_vis_x3f_481_);
lean_dec(v___x_480_);
lean_dec(v___x_479_);
lean_dec(v_type_478_);
lean_dec(v_structTy_477_);
v_a_676_ = lean_ctor_get(v___x_661_, 0);
v_a_677_ = lean_ctor_get(v___x_661_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_661_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_inc(v_a_676_);
lean_dec(v___x_661_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
else
{
lean_object* v___x_702_; 
lean_dec(v_vis_x3f_481_);
lean_dec(v___x_480_);
lean_dec(v___x_479_);
lean_dec(v_type_478_);
lean_dec(v_structTy_477_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_b_486_);
lean_ctor_set(v___x_702_, 1, v___y_488_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___boxed(lean_object* v_structTy_703_, lean_object* v_type_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_vis_x3f_707_, lean_object* v_structId_708_, lean_object* v_as_709_, lean_object* v_i_710_, lean_object* v_stop_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_i_boxed_715_; size_t v_stop_boxed_716_; lean_object* v_res_717_; 
v_i_boxed_715_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_stop_boxed_716_ = lean_unbox_usize(v_stop_711_);
lean_dec(v_stop_711_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(v_structTy_703_, v_type_704_, v___x_705_, v___x_706_, v_vis_x3f_707_, v_structId_708_, v_as_709_, v_i_boxed_715_, v_stop_boxed_716_, v_b_712_, v___y_713_, v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec_ref(v_as_709_);
lean_dec(v_structId_708_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(lean_object* v_structTy_718_, lean_object* v_type_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_vis_x3f_722_, lean_object* v_structId_723_, lean_object* v_as_724_, size_t v_i_725_, size_t v_stop_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_eq(v_i_725_, v_stop_726_);
if (v___x_730_ == 0)
{
lean_object* v_cmds_731_; lean_object* v_fields_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_942_; 
v_cmds_731_ = lean_ctor_get(v_b_727_, 0);
v_fields_732_ = lean_ctor_get(v_b_727_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_b_727_);
if (v_isSharedCheck_942_ == 0)
{
v___x_734_ = v_b_727_;
v_isShared_735_ = v_isSharedCheck_942_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_fields_732_);
lean_inc(v_cmds_731_);
lean_dec(v_b_727_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_942_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_895_; uint8_t v___x_926_; 
v___x_736_ = lean_array_uget_borrowed(v_as_724_, v_i_725_);
v___x_737_ = l_Lean_TSyntax_getId(v___x_736_);
lean_inc(v___x_737_);
lean_inc(v___x_736_);
v___x_738_ = l_Lake_Name_quoteFrom(v___x_736_, v___x_737_, v___x_730_);
v___x_926_ = l_Lean_Name_hasMacroScopes(v___x_737_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_723_, v___x_737_);
v___y_895_ = v___x_927_;
goto v___jp_894_;
}
else
{
lean_object* v_view_928_; lean_object* v_name_929_; lean_object* v_imported_930_; lean_object* v_ctx_931_; lean_object* v_scopes_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_941_; 
v_view_928_ = l_Lean_extractMacroScopes(v___x_737_);
v_name_929_ = lean_ctor_get(v_view_928_, 0);
v_imported_930_ = lean_ctor_get(v_view_928_, 1);
v_ctx_931_ = lean_ctor_get(v_view_928_, 2);
v_scopes_932_ = lean_ctor_get(v_view_928_, 3);
v_isSharedCheck_941_ = !lean_is_exclusive(v_view_928_);
if (v_isSharedCheck_941_ == 0)
{
v___x_934_ = v_view_928_;
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_scopes_932_);
lean_inc(v_ctx_931_);
lean_inc(v_imported_930_);
lean_inc(v_name_929_);
lean_dec(v_view_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_723_, v_name_929_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_imported_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_ctx_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_scopes_932_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_MacroScopesView_review(v___x_938_);
v___y_895_ = v___x_939_;
goto v___jp_894_;
}
}
}
v___jp_739_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_ref_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc_ref(v___y_752_);
v___x_758_ = l_Array_append___redArg(v___y_752_, v___y_757_);
lean_dec_ref(v___y_757_);
lean_inc_n(v___y_753_, 4);
lean_inc_n(v___y_747_, 18);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___y_747_);
lean_ctor_set(v___x_759_, 1, v___y_753_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_inc_n(v___y_744_, 11);
lean_inc(v___y_741_);
v___x_760_ = l_Lean_Syntax_node7(v___y_747_, v___y_741_, v___y_744_, v___y_744_, v___x_759_, v___y_744_, v___y_744_, v___y_744_, v___y_744_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_755_, 4);
lean_inc_ref_n(v___y_745_, 9);
lean_inc_ref_n(v___y_751_, 9);
v___x_762_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___y_755_, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_765_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___y_747_, v___x_765_, v___y_744_);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_747_);
lean_ctor_set(v___x_767_, 1, v___x_761_);
v___x_768_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_769_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___y_755_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___y_747_, v___x_769_, v___y_746_, v___y_744_);
v___x_771_ = l_Lean_Syntax_node1(v___y_747_, v___y_753_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_773_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___y_755_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_775_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_747_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_779_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_778_);
v___x_780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_742_, 2);
lean_inc_n(v___y_748_, 2);
v___x_782_ = l_Lean_addMacroScope(v___y_748_, v___x_781_, v___y_742_);
v___x_783_ = lean_box(0);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_785_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_785_, 0, v___y_747_);
lean_ctor_set(v___x_785_, 1, v___x_780_);
lean_ctor_set(v___x_785_, 2, v___x_782_);
lean_ctor_set(v___x_785_, 3, v___x_784_);
lean_inc(v_type_719_);
lean_inc(v___x_738_);
lean_inc(v_structTy_718_);
v___x_786_ = l_Lean_Syntax_node3(v___y_747_, v___y_753_, v_structTy_718_, v___x_738_, v_type_719_);
v___x_787_ = l_Lean_Syntax_node2(v___y_747_, v___x_779_, v___x_785_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node2(v___y_747_, v___x_775_, v___x_777_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___y_747_, v___x_773_, v___y_744_, v___x_788_);
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_791_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___y_755_, v___x_790_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___y_747_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_795_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_794_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_747_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_inc(v___x_720_);
v___x_798_ = l_Lean_Syntax_node1(v___y_747_, v___y_753_, v___x_720_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___y_747_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_Syntax_node3(v___y_747_, v___x_795_, v___x_797_, v___x_798_, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_804_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_802_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node2(v___y_747_, v___x_804_, v___y_744_, v___y_744_);
v_ref_806_ = l_Lean_replaceRef(v_fields_732_, v___y_750_);
lean_inc(v_ref_806_);
lean_inc(v___y_756_);
lean_inc(v___y_740_);
lean_inc(v___y_743_);
v___x_807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_807_, 0, v___y_743_);
lean_ctor_set(v___x_807_, 1, v___y_748_);
lean_ctor_set(v___x_807_, 2, v___y_742_);
lean_ctor_set(v___x_807_, 3, v___y_740_);
lean_ctor_set(v___x_807_, 4, v___y_756_);
lean_ctor_set(v___x_807_, 5, v_ref_806_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_730_, v_ref_806_, v___x_807_, v___y_754_);
lean_dec_ref(v___x_807_);
lean_dec(v_ref_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_n(v_a_809_, 30);
v_a_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc(v_a_810_);
lean_dec_ref(v___x_808_);
lean_inc(v___y_744_);
lean_inc_n(v___y_747_, 2);
v___x_811_ = l_Lean_Syntax_node4(v___y_747_, v___x_791_, v___x_793_, v___x_801_, v___x_805_, v___y_744_);
v___x_812_ = l_Lean_Syntax_node6(v___y_747_, v___x_762_, v___x_766_, v___x_767_, v___y_744_, v___x_771_, v___x_789_, v___x_811_);
lean_inc(v___y_749_);
v___x_813_ = l_Lean_Syntax_node2(v___y_747_, v___y_749_, v___x_760_, v___x_812_);
v___x_814_ = lean_array_push(v_cmds_731_, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_745_, 7);
lean_inc_ref_n(v___y_751_, 7);
v___x_816_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_815_);
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_818_, 0, v_a_809_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_742_, 5);
lean_inc_n(v___y_748_, 5);
v___x_821_ = l_Lean_addMacroScope(v___y_748_, v___x_820_, v___y_742_);
v___x_822_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_822_, 0, v_a_809_);
lean_ctor_set(v___x_822_, 1, v___x_819_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
lean_ctor_set(v___x_822_, 3, v___x_783_);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_824_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_823_);
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_826_, 0, v_a_809_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
lean_inc_ref(v___y_752_);
lean_inc_n(v___y_753_, 7);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v_a_809_);
lean_ctor_set(v___x_827_, 1, v___y_753_);
lean_ctor_set(v___x_827_, 2, v___y_752_);
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_829_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_831_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_830_);
v___x_832_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_833_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_832_);
v___x_834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_836_ = l_Lean_addMacroScope(v___y_748_, v___x_835_, v___y_742_);
v___x_837_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_837_, 0, v_a_809_);
lean_ctor_set(v___x_837_, 1, v___x_834_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
lean_ctor_set(v___x_837_, 3, v___x_783_);
lean_inc_ref_n(v___x_827_, 16);
lean_inc_n(v___x_833_, 2);
v___x_838_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_837_, v___x_827_);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_840_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_839_);
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_809_);
lean_ctor_set(v___x_841_, 1, v___x_792_);
lean_inc_ref_n(v___x_841_, 2);
lean_inc_n(v___x_840_, 2);
v___x_842_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_827_, v___x_738_);
v___x_843_ = l_Lean_Syntax_node3(v_a_809_, v___y_753_, v___x_827_, v___x_827_, v___x_842_);
lean_inc_n(v___x_831_, 2);
v___x_844_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_838_, v___x_843_);
v___x_845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_847_ = l_Lean_addMacroScope(v___y_748_, v___x_846_, v___y_742_);
v___x_848_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_848_, 0, v_a_809_);
lean_ctor_set(v___x_848_, 1, v___x_845_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
lean_ctor_set(v___x_848_, 3, v___x_783_);
v___x_849_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_848_, v___x_827_);
lean_inc(v___x_721_);
v___x_850_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_827_, v___x_721_);
v___x_851_ = l_Lean_Syntax_node3(v_a_809_, v___y_753_, v___x_827_, v___x_827_, v___x_850_);
v___x_852_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_849_, v___x_851_);
v___x_853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_855_ = l_Lean_addMacroScope(v___y_748_, v___x_854_, v___y_742_);
v___x_856_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_856_, 0, v_a_809_);
lean_ctor_set(v___x_856_, 1, v___x_853_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_783_);
v___x_857_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_856_, v___x_827_);
v___x_858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_859_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_827_, v___x_858_);
v___x_860_ = l_Lean_Syntax_node3(v_a_809_, v___y_753_, v___x_827_, v___x_827_, v___x_859_);
v___x_861_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_857_, v___x_860_);
v___x_862_ = l_Lean_Syntax_node6(v_a_809_, v___y_753_, v___x_844_, v___x_827_, v___x_852_, v___x_827_, v___x_861_, v___x_827_);
v___x_863_ = l_Lean_Syntax_node1(v_a_809_, v___x_829_, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_865_ = l_Lean_Name_mkStr4(v___y_751_, v___y_745_, v___x_763_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node1(v_a_809_, v___x_865_, v___x_827_);
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v_a_809_);
lean_ctor_set(v___x_867_, 1, v___x_776_);
v___x_868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_870_ = l_Lean_addMacroScope(v___y_748_, v___x_869_, v___y_742_);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_872_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_872_, 0, v_a_809_);
lean_ctor_set(v___x_872_, 1, v___x_868_);
lean_ctor_set(v___x_872_, 2, v___x_870_);
lean_ctor_set(v___x_872_, 3, v___x_871_);
v___x_873_ = l_Lean_Syntax_node2(v_a_809_, v___y_753_, v___x_867_, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_809_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_Syntax_node6(v_a_809_, v___x_824_, v___x_826_, v___x_827_, v___x_863_, v___x_866_, v___x_873_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node1(v_a_809_, v___y_753_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node4(v_a_809_, v___x_816_, v_fields_732_, v___x_818_, v___x_822_, v___x_877_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_878_);
lean_ctor_set(v___x_734_, 0, v___x_814_);
v___x_880_ = v___x_734_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_add(v_i_725_, v___x_881_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(v_structTy_718_, v_type_719_, v___x_720_, v___x_721_, v_vis_x3f_722_, v_structId_723_, v_as_724_, v___x_882_, v_stop_726_, v___x_880_, v___y_728_, v_a_810_);
return v___x_883_;
}
}
else
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v___x_805_);
lean_dec(v___x_801_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_791_);
lean_dec(v___x_789_);
lean_dec(v___x_771_);
lean_dec_ref(v___x_767_);
lean_dec(v___x_766_);
lean_dec(v___x_762_);
lean_dec(v___x_760_);
lean_dec(v___y_747_);
lean_dec(v___y_744_);
lean_dec(v___x_738_);
lean_del_object(v___x_734_);
lean_dec(v_fields_732_);
lean_dec_ref(v_cmds_731_);
lean_dec(v_vis_x3f_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec(v_type_719_);
lean_dec(v_structTy_718_);
v_a_885_ = lean_ctor_get(v___x_808_, 0);
v_a_886_ = lean_ctor_get(v___x_808_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_808_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_inc(v_a_885_);
lean_dec(v___x_808_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
v___jp_894_:
{
lean_object* v_methods_896_; lean_object* v_quotContext_897_; lean_object* v_currMacroScope_898_; lean_object* v_currRecDepth_899_; lean_object* v_maxRecDepth_900_; lean_object* v_ref_901_; lean_object* v___x_902_; 
v_methods_896_ = lean_ctor_get(v___y_728_, 0);
v_quotContext_897_ = lean_ctor_get(v___y_728_, 1);
v_currMacroScope_898_ = lean_ctor_get(v___y_728_, 2);
v_currRecDepth_899_ = lean_ctor_get(v___y_728_, 3);
v_maxRecDepth_900_ = lean_ctor_get(v___y_728_, 4);
v_ref_901_ = lean_ctor_get(v___y_728_, 5);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_730_, v_ref_901_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc_n(v_a_903_, 2);
v_a_904_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_a_904_);
lean_dec_ref(v___x_902_);
v___x_905_ = l_Lean_mkIdentFrom(v___x_736_, v___y_895_, v___x_730_);
v___x_906_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_907_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_908_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_911_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_912_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_913_, 0, v_a_903_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
if (lean_obj_tag(v_vis_x3f_722_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_915_; 
v_val_914_ = lean_ctor_get(v_vis_x3f_722_, 0);
lean_inc(v_val_914_);
v___x_915_ = l_Array_mkArray1___redArg(v_val_914_);
v___y_740_ = v_currRecDepth_899_;
v___y_741_ = v___x_910_;
v___y_742_ = v_currMacroScope_898_;
v___y_743_ = v_methods_896_;
v___y_744_ = v___x_913_;
v___y_745_ = v___x_907_;
v___y_746_ = v___x_905_;
v___y_747_ = v_a_903_;
v___y_748_ = v_quotContext_897_;
v___y_749_ = v___x_909_;
v___y_750_ = v_ref_901_;
v___y_751_ = v___x_906_;
v___y_752_ = v___x_912_;
v___y_753_ = v___x_911_;
v___y_754_ = v_a_904_;
v___y_755_ = v___x_908_;
v___y_756_ = v_maxRecDepth_900_;
v___y_757_ = v___x_915_;
goto v___jp_739_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_740_ = v_currRecDepth_899_;
v___y_741_ = v___x_910_;
v___y_742_ = v_currMacroScope_898_;
v___y_743_ = v_methods_896_;
v___y_744_ = v___x_913_;
v___y_745_ = v___x_907_;
v___y_746_ = v___x_905_;
v___y_747_ = v_a_903_;
v___y_748_ = v_quotContext_897_;
v___y_749_ = v___x_909_;
v___y_750_ = v_ref_901_;
v___y_751_ = v___x_906_;
v___y_752_ = v___x_912_;
v___y_753_ = v___x_911_;
v___y_754_ = v_a_904_;
v___y_755_ = v___x_908_;
v___y_756_ = v_maxRecDepth_900_;
v___y_757_ = v___x_916_;
goto v___jp_739_;
}
}
else
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___y_895_);
lean_dec(v___x_738_);
lean_del_object(v___x_734_);
lean_dec(v_fields_732_);
lean_dec_ref(v_cmds_731_);
lean_dec(v_vis_x3f_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec(v_type_719_);
lean_dec(v_structTy_718_);
v_a_917_ = lean_ctor_get(v___x_902_, 0);
v_a_918_ = lean_ctor_get(v___x_902_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_902_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_inc(v_a_917_);
lean_dec(v___x_902_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_vis_x3f_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec(v_type_719_);
lean_dec(v_structTy_718_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_b_727_);
lean_ctor_set(v___x_943_, 1, v___y_729_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___boxed(lean_object* v_structTy_944_, lean_object* v_type_945_, lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_vis_x3f_948_, lean_object* v_structId_949_, lean_object* v_as_950_, lean_object* v_i_951_, lean_object* v_stop_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_i_boxed_956_; size_t v_stop_boxed_957_; lean_object* v_res_958_; 
v_i_boxed_956_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_stop_boxed_957_ = lean_unbox_usize(v_stop_952_);
lean_dec(v_stop_952_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_944_, v_type_945_, v___x_946_, v___x_947_, v_vis_x3f_948_, v_structId_949_, v_as_950_, v_i_boxed_956_, v_stop_boxed_957_, v_b_953_, v___y_954_, v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
lean_dec(v_structId_949_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(lean_object* v_structId_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = l_Lean_TSyntax_getId(v_structId_960_);
v___x_963_ = l_Lean_Name_append(v___x_962_, v_x_961_);
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___closed__0));
v___x_965_ = l_Lean_Name_str___override(v___x_963_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___boxed(lean_object* v_structId_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_966_, v_x_967_);
lean_dec(v_structId_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(lean_object* v_structId_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_972_ = l_Lean_TSyntax_getId(v_structId_970_);
v___x_973_ = l_Lean_Name_append(v___x_972_, v_x_971_);
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___closed__0));
v___x_975_ = l_Lean_Name_str___override(v___x_973_, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___boxed(lean_object* v_structId_976_, lean_object* v_x_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_976_, v_x_977_);
lean_dec(v_structId_976_);
return v_res_978_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
v___x_984_ = l_Lean_mkCIdent(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_987_ = l_String_toRawSubstring_x27(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6));
v___x_992_ = l_String_toRawSubstring_x27(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__14));
v___x_1003_ = l_String_toRawSubstring_x27(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__17));
v___x_1007_ = l_String_toRawSubstring_x27(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23));
v___x_1016_ = l_String_toRawSubstring_x27(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0));
v___x_1020_ = l_String_toRawSubstring_x27(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31));
v___x_1028_ = l_String_toRawSubstring_x27(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41));
v___x_1049_ = l_String_toRawSubstring_x27(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48));
v___x_1064_ = l_String_toRawSubstring_x27(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53));
v___x_1071_ = l_String_toRawSubstring_x27(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60));
v___x_1086_ = l_String_toRawSubstring_x27(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64));
v___x_1092_ = l_String_toRawSubstring_x27(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69));
v___x_1103_ = l_String_toRawSubstring_x27(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72));
v___x_1108_ = l_String_toRawSubstring_x27(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(lean_object* v_structTy_1114_, lean_object* v___x_1115_, lean_object* v_vis_x3f_1116_, lean_object* v_structId_1117_, lean_object* v_as_1118_, size_t v_i_1119_, size_t v_stop_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___y_1131_; uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1134_ == 0)
{
lean_object* v_cmds_1135_; lean_object* v_fields_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1889_; 
v_cmds_1135_ = lean_ctor_get(v_b_1121_, 0);
v_fields_1136_ = lean_ctor_get(v_b_1121_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_b_1121_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1138_ = v_b_1121_;
v_isShared_1139_ = v_isSharedCheck_1889_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_fields_1136_);
lean_inc(v_cmds_1135_);
lean_dec(v_b_1121_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1889_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v_id_1141_; lean_object* v_ids_1142_; lean_object* v_type_1143_; lean_object* v_defVal_1144_; uint8_t v_parent_1145_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___x_1647_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1853_; uint8_t v___x_1873_; 
v___x_1140_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
v_id_1141_ = lean_ctor_get(v___x_1140_, 2);
v_ids_1142_ = lean_ctor_get(v___x_1140_, 3);
v_type_1143_ = lean_ctor_get(v___x_1140_, 4);
v_defVal_1144_ = lean_ctor_get(v___x_1140_, 5);
v_parent_1145_ = lean_ctor_get_uint8(v___x_1140_, sizeof(void*)*7);
v___x_1647_ = l_Lean_TSyntax_getId(v_id_1141_);
v___x_1873_ = l_Lean_Name_hasMacroScopes(v___x_1647_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_inc(v___x_1647_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1117_, v___x_1647_);
v___y_1853_ = v___x_1874_;
goto v___jp_1852_;
}
else
{
lean_object* v_view_1875_; lean_object* v_name_1876_; lean_object* v_imported_1877_; lean_object* v_ctx_1878_; lean_object* v_scopes_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1888_; 
lean_inc(v___x_1647_);
v_view_1875_ = l_Lean_extractMacroScopes(v___x_1647_);
v_name_1876_ = lean_ctor_get(v_view_1875_, 0);
v_imported_1877_ = lean_ctor_get(v_view_1875_, 1);
v_ctx_1878_ = lean_ctor_get(v_view_1875_, 2);
v_scopes_1879_ = lean_ctor_get(v_view_1875_, 3);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_view_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1881_ = v_view_1875_;
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_scopes_1879_);
lean_inc(v_ctx_1878_);
lean_inc(v_imported_1877_);
lean_inc(v_name_1876_);
lean_dec(v_view_1875_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1117_, v_name_1876_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_imported_1877_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_ctx_1878_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_scopes_1879_);
v___x_1885_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_MacroScopesView_review(v___x_1885_);
v___y_1853_ = v___x_1886_;
goto v___jp_1852_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_ref_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_inc_ref(v___y_1159_);
v___x_1187_ = l_Array_append___redArg(v___y_1159_, v___y_1186_);
lean_dec_ref(v___y_1186_);
lean_inc_n(v___y_1169_, 4);
lean_inc_n(v___y_1185_, 18);
v___x_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1185_);
lean_ctor_set(v___x_1188_, 1, v___y_1169_);
lean_ctor_set(v___x_1188_, 2, v___x_1187_);
lean_inc_n(v___y_1164_, 11);
lean_inc(v___y_1158_);
v___x_1189_ = l_Lean_Syntax_node7(v___y_1185_, v___y_1158_, v___y_1164_, v___y_1164_, v___x_1188_, v___y_1164_, v___y_1164_, v___y_1164_, v___y_1164_);
v___x_1190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1147_, 3);
lean_inc_ref_n(v___y_1160_, 6);
lean_inc_ref_n(v___y_1173_, 6);
v___x_1191_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1147_, v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1162_, 2);
v___x_1193_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1162_, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node1(v___y_1185_, v___x_1193_, v___y_1164_);
v___x_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___y_1185_);
lean_ctor_set(v___x_1195_, 1, v___x_1190_);
v___x_1196_ = l_Lean_Syntax_node2(v___y_1185_, v___y_1155_, v___y_1182_, v___y_1164_);
v___x_1197_ = l_Lean_Syntax_node1(v___y_1185_, v___y_1169_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1199_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1147_, v___x_1198_);
lean_inc_ref(v___y_1170_);
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___y_1185_);
lean_ctor_set(v___x_1200_, 1, v___y_1170_);
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1157_, 2);
lean_inc_n(v___y_1168_, 2);
v___x_1204_ = l_Lean_addMacroScope(v___y_1168_, v___x_1203_, v___y_1157_);
lean_inc_ref(v___y_1165_);
v___x_1205_ = l_Lean_Name_mkStr2(v___y_1165_, v___x_1201_);
lean_inc(v___y_1177_);
lean_inc(v___x_1205_);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___y_1177_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_inc(v___y_1166_);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___y_1166_);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1185_);
lean_ctor_set(v___x_1210_, 1, v___x_1202_);
lean_ctor_set(v___x_1210_, 2, v___x_1204_);
lean_ctor_set(v___x_1210_, 3, v___x_1209_);
lean_inc(v_type_1143_);
lean_inc(v___y_1148_);
lean_inc(v_structTy_1114_);
v___x_1211_ = l_Lean_Syntax_node3(v___y_1185_, v___y_1169_, v_structTy_1114_, v___y_1148_, v_type_1143_);
v___x_1212_ = l_Lean_Syntax_node2(v___y_1185_, v___y_1151_, v___x_1210_, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node2(v___y_1185_, v___y_1172_, v___x_1200_, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node2(v___y_1185_, v___x_1199_, v___y_1164_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1216_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1147_, v___x_1215_);
lean_inc_ref(v___y_1181_);
v___x_1217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1185_);
lean_ctor_set(v___x_1217_, 1, v___y_1181_);
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1219_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1162_, v___x_1218_);
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1185_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_inc(v___y_1180_);
v___x_1222_ = l_Lean_Syntax_node1(v___y_1185_, v___y_1169_, v___y_1180_);
v___x_1223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1185_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node3(v___y_1185_, v___x_1219_, v___x_1221_, v___x_1222_, v___x_1224_);
v___x_1226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1228_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___x_1226_, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node2(v___y_1185_, v___x_1228_, v___y_1164_, v___y_1164_);
v_ref_1230_ = l_Lean_replaceRef(v_fields_1136_, v___y_1167_);
lean_inc(v_ref_1230_);
lean_inc(v___y_1176_);
lean_inc(v___y_1150_);
lean_inc(v___y_1183_);
v___x_1231_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1231_, 0, v___y_1183_);
lean_ctor_set(v___x_1231_, 1, v___y_1168_);
lean_ctor_set(v___x_1231_, 2, v___y_1157_);
lean_ctor_set(v___x_1231_, 3, v___y_1150_);
lean_ctor_set(v___x_1231_, 4, v___y_1176_);
lean_ctor_set(v___x_1231_, 5, v_ref_1230_);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1134_, v_ref_1230_, v___x_1231_, v___y_1152_);
lean_dec_ref(v___x_1231_);
lean_dec(v_ref_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_n(v_a_1233_, 30);
v_a_1234_ = lean_ctor_get(v___x_1232_, 1);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1232_);
lean_inc(v___y_1164_);
lean_inc_n(v___y_1185_, 2);
v___x_1235_ = l_Lean_Syntax_node4(v___y_1185_, v___x_1216_, v___x_1217_, v___x_1225_, v___x_1229_, v___y_1164_);
v___x_1236_ = l_Lean_Syntax_node6(v___y_1185_, v___x_1191_, v___x_1194_, v___x_1195_, v___y_1164_, v___x_1197_, v___x_1214_, v___x_1235_);
lean_inc(v___y_1154_);
v___x_1237_ = l_Lean_Syntax_node2(v___y_1185_, v___y_1154_, v___x_1189_, v___x_1236_);
v___x_1238_ = lean_array_push(v___y_1153_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1160_);
lean_inc_ref(v___y_1173_);
v___x_1240_ = l_Lean_Name_mkStr4(v___y_1173_, v___y_1160_, v___y_1162_, v___x_1239_);
v___x_1241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_a_1233_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1157_, 5);
lean_inc_n(v___y_1168_, 5);
v___x_1245_ = l_Lean_addMacroScope(v___y_1168_, v___x_1244_, v___y_1157_);
lean_inc_n(v___y_1166_, 5);
v___x_1246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1233_);
lean_ctor_set(v___x_1246_, 1, v___x_1243_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
lean_ctor_set(v___x_1246_, 3, v___y_1166_);
lean_inc_ref(v___y_1184_);
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1233_);
lean_ctor_set(v___x_1247_, 1, v___y_1184_);
lean_inc_ref(v___y_1159_);
lean_inc_n(v___y_1169_, 7);
v___x_1248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1233_);
lean_ctor_set(v___x_1248_, 1, v___y_1169_);
lean_ctor_set(v___x_1248_, 2, v___y_1159_);
v___x_1249_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1251_ = l_Lean_addMacroScope(v___y_1168_, v___x_1250_, v___y_1157_);
v___x_1252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1233_);
lean_ctor_set(v___x_1252_, 1, v___x_1249_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
lean_ctor_set(v___x_1252_, 3, v___y_1166_);
lean_inc_ref_n(v___x_1248_, 16);
lean_inc_n(v___y_1149_, 2);
v___x_1253_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1149_, v___x_1252_, v___x_1248_);
lean_inc_ref(v___y_1181_);
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1233_);
lean_ctor_set(v___x_1254_, 1, v___y_1181_);
lean_inc_ref_n(v___x_1254_, 2);
lean_inc_n(v___y_1179_, 2);
v___x_1255_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1179_, v___x_1254_, v___x_1248_, v___y_1148_);
v___x_1256_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1169_, v___x_1248_, v___x_1248_, v___x_1255_);
lean_inc_n(v___y_1174_, 2);
v___x_1257_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1174_, v___x_1253_, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1260_ = l_Lean_addMacroScope(v___y_1168_, v___x_1259_, v___y_1157_);
v___x_1261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1233_);
lean_ctor_set(v___x_1261_, 1, v___x_1258_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
lean_ctor_set(v___x_1261_, 3, v___y_1166_);
v___x_1262_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1149_, v___x_1261_, v___x_1248_);
lean_inc(v___y_1161_);
v___x_1263_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1179_, v___x_1254_, v___x_1248_, v___y_1161_);
v___x_1264_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1169_, v___x_1248_, v___x_1248_, v___x_1263_);
v___x_1265_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1174_, v___x_1262_, v___x_1264_);
v___x_1266_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_1267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_1268_ = l_Lean_addMacroScope(v___y_1168_, v___x_1267_, v___y_1157_);
v___x_1269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1233_);
lean_ctor_set(v___x_1269_, 1, v___x_1266_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
lean_ctor_set(v___x_1269_, 3, v___y_1166_);
v___x_1270_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1149_, v___x_1269_, v___x_1248_);
v___x_1271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_1272_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1179_, v___x_1254_, v___x_1248_, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_node3(v_a_1233_, v___y_1169_, v___x_1248_, v___x_1248_, v___x_1272_);
v___x_1274_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1174_, v___x_1270_, v___x_1273_);
v___x_1275_ = l_Lean_Syntax_node6(v_a_1233_, v___y_1169_, v___x_1257_, v___x_1248_, v___x_1265_, v___x_1248_, v___x_1274_, v___x_1248_);
v___x_1276_ = l_Lean_Syntax_node1(v_a_1233_, v___y_1175_, v___x_1275_);
v___x_1277_ = l_Lean_Syntax_node1(v_a_1233_, v___y_1156_, v___x_1248_);
lean_inc_ref(v___y_1170_);
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_a_1233_);
lean_ctor_set(v___x_1278_, 1, v___y_1170_);
v___x_1279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1280_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1282_ = l_Lean_addMacroScope(v___y_1168_, v___x_1281_, v___y_1157_);
lean_inc_ref(v___y_1165_);
v___x_1283_ = l_Lean_Name_mkStr2(v___y_1165_, v___x_1279_);
lean_inc(v___y_1177_);
lean_inc(v___x_1283_);
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v___y_1177_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___y_1166_);
v___x_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1284_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1288_, 0, v_a_1233_);
lean_ctor_set(v___x_1288_, 1, v___x_1280_);
lean_ctor_set(v___x_1288_, 2, v___x_1282_);
lean_ctor_set(v___x_1288_, 3, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node2(v_a_1233_, v___y_1169_, v___x_1278_, v___x_1288_);
lean_inc_ref(v___y_1163_);
v___x_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_a_1233_);
lean_ctor_set(v___x_1290_, 1, v___y_1163_);
v___x_1291_ = l_Lean_Syntax_node6(v_a_1233_, v___y_1178_, v___x_1247_, v___x_1248_, v___x_1276_, v___x_1277_, v___x_1289_, v___x_1290_);
v___x_1292_ = l_Lean_Syntax_node1(v_a_1233_, v___y_1169_, v___x_1291_);
v___x_1293_ = l_Lean_Syntax_node4(v_a_1233_, v___x_1240_, v_fields_1136_, v___x_1242_, v___x_1246_, v___x_1292_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1293_);
lean_ctor_set(v___x_1138_, 0, v___x_1238_);
v___x_1295_ = v___x_1138_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_dec_lt(v___x_1296_, v___y_1171_);
if (v___x_1297_ == 0)
{
lean_dec(v___y_1180_);
lean_dec(v___y_1171_);
lean_dec(v___y_1161_);
v_a_1125_ = v___x_1295_;
v_a_1126_ = v_a_1234_;
goto v___jp_1124_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_le(v___y_1171_, v___y_1171_);
if (v___x_1298_ == 0)
{
if (v___x_1297_ == 0)
{
lean_dec(v___y_1180_);
lean_dec(v___y_1171_);
lean_dec(v___y_1161_);
v_a_1125_ = v___x_1295_;
v_a_1126_ = v_a_1234_;
goto v___jp_1124_;
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_of_nat(v___y_1171_);
lean_dec(v___y_1171_);
lean_inc(v_vis_x3f_1116_);
lean_inc(v_type_1143_);
lean_inc(v_structTy_1114_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1114_, v_type_1143_, v___y_1180_, v___y_1161_, v_vis_x3f_1116_, v_structId_1117_, v_ids_1142_, v___x_1299_, v___x_1300_, v___x_1295_, v___y_1122_, v_a_1234_);
v___y_1131_ = v___x_1301_;
goto v___jp_1130_;
}
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_of_nat(v___y_1171_);
lean_dec(v___y_1171_);
lean_inc(v_vis_x3f_1116_);
lean_inc(v_type_1143_);
lean_inc(v_structTy_1114_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1114_, v_type_1143_, v___y_1180_, v___y_1161_, v_vis_x3f_1116_, v_structId_1117_, v_ids_1142_, v___x_1302_, v___x_1303_, v___x_1295_, v___y_1122_, v_a_1234_);
v___y_1131_ = v___x_1304_;
goto v___jp_1130_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___x_1229_);
lean_dec(v___x_1225_);
lean_dec_ref(v___x_1217_);
lean_dec(v___x_1216_);
lean_dec(v___x_1214_);
lean_dec(v___x_1197_);
lean_dec_ref(v___x_1195_);
lean_dec(v___x_1194_);
lean_dec(v___x_1191_);
lean_dec(v___x_1189_);
lean_dec(v___y_1185_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec(v___y_1171_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1149_);
lean_dec(v___y_1148_);
lean_del_object(v___x_1138_);
lean_dec(v_fields_1136_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1306_ = lean_ctor_get(v___x_1232_, 0);
v_a_1307_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1232_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_inc(v_a_1306_);
lean_dec(v___x_1232_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1306_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1134_, v___y_1335_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_n(v_a_1355_, 2);
v_a_1356_ = lean_ctor_get(v___x_1354_, 1);
lean_inc(v_a_1356_);
lean_dec_ref(v___x_1354_);
v___x_1357_ = l_Lean_mkIdentFrom(v___y_1350_, v___y_1353_, v___x_1134_);
lean_dec(v___y_1350_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1337_);
v___x_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1355_);
lean_ctor_set(v___x_1358_, 1, v___y_1337_);
lean_ctor_set(v___x_1358_, 2, v___y_1328_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1359_; lean_object* v___x_1360_; 
v_val_1359_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1359_);
v___x_1360_ = l_Array_mkArray1___redArg(v_val_1359_);
v___y_1147_ = v___y_1317_;
v___y_1148_ = v___y_1316_;
v___y_1149_ = v___y_1318_;
v___y_1150_ = v___y_1320_;
v___y_1151_ = v___y_1321_;
v___y_1152_ = v_a_1356_;
v___y_1153_ = v___y_1322_;
v___y_1154_ = v___y_1324_;
v___y_1155_ = v___y_1323_;
v___y_1156_ = v___y_1325_;
v___y_1157_ = v___y_1326_;
v___y_1158_ = v___y_1327_;
v___y_1159_ = v___y_1328_;
v___y_1160_ = v___y_1329_;
v___y_1161_ = v___y_1330_;
v___y_1162_ = v___y_1331_;
v___y_1163_ = v___y_1332_;
v___y_1164_ = v___x_1358_;
v___y_1165_ = v___y_1333_;
v___y_1166_ = v___y_1334_;
v___y_1167_ = v___y_1335_;
v___y_1168_ = v___y_1336_;
v___y_1169_ = v___y_1337_;
v___y_1170_ = v___y_1338_;
v___y_1171_ = v___y_1339_;
v___y_1172_ = v___y_1340_;
v___y_1173_ = v___y_1341_;
v___y_1174_ = v___y_1342_;
v___y_1175_ = v___y_1343_;
v___y_1176_ = v___y_1344_;
v___y_1177_ = v___y_1345_;
v___y_1178_ = v___y_1347_;
v___y_1179_ = v___y_1346_;
v___y_1180_ = v___y_1348_;
v___y_1181_ = v___y_1349_;
v___y_1182_ = v___x_1357_;
v___y_1183_ = v___y_1351_;
v___y_1184_ = v___y_1352_;
v___y_1185_ = v_a_1355_;
v___y_1186_ = v___x_1360_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_mk_empty_array_with_capacity(v___y_1319_);
v___y_1147_ = v___y_1317_;
v___y_1148_ = v___y_1316_;
v___y_1149_ = v___y_1318_;
v___y_1150_ = v___y_1320_;
v___y_1151_ = v___y_1321_;
v___y_1152_ = v_a_1356_;
v___y_1153_ = v___y_1322_;
v___y_1154_ = v___y_1324_;
v___y_1155_ = v___y_1323_;
v___y_1156_ = v___y_1325_;
v___y_1157_ = v___y_1326_;
v___y_1158_ = v___y_1327_;
v___y_1159_ = v___y_1328_;
v___y_1160_ = v___y_1329_;
v___y_1161_ = v___y_1330_;
v___y_1162_ = v___y_1331_;
v___y_1163_ = v___y_1332_;
v___y_1164_ = v___x_1358_;
v___y_1165_ = v___y_1333_;
v___y_1166_ = v___y_1334_;
v___y_1167_ = v___y_1335_;
v___y_1168_ = v___y_1336_;
v___y_1169_ = v___y_1337_;
v___y_1170_ = v___y_1338_;
v___y_1171_ = v___y_1339_;
v___y_1172_ = v___y_1340_;
v___y_1173_ = v___y_1341_;
v___y_1174_ = v___y_1342_;
v___y_1175_ = v___y_1343_;
v___y_1176_ = v___y_1344_;
v___y_1177_ = v___y_1345_;
v___y_1178_ = v___y_1347_;
v___y_1179_ = v___y_1346_;
v___y_1180_ = v___y_1348_;
v___y_1181_ = v___y_1349_;
v___y_1182_ = v___x_1357_;
v___y_1183_ = v___y_1351_;
v___y_1184_ = v___y_1352_;
v___y_1185_ = v_a_1355_;
v___y_1186_ = v___x_1361_;
goto v___jp_1146_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v___y_1353_);
lean_dec(v___y_1350_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec(v___y_1325_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1318_);
lean_dec(v___y_1316_);
lean_del_object(v___x_1138_);
lean_dec(v_fields_1136_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1362_ = lean_ctor_get(v___x_1354_, 0);
v_a_1363_ = lean_ctor_get(v___x_1354_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1354_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_inc(v_a_1362_);
lean_dec(v___x_1354_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1362_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
v___jp_1371_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_inc_ref(v___y_1382_);
v___x_1410_ = l_Array_append___redArg(v___y_1382_, v___y_1409_);
lean_dec_ref(v___y_1409_);
lean_inc_n(v___y_1391_, 4);
lean_inc_n(v___y_1406_, 18);
v___x_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1406_);
lean_ctor_set(v___x_1411_, 1, v___y_1391_);
lean_ctor_set(v___x_1411_, 2, v___x_1410_);
lean_inc_n(v___y_1395_, 11);
lean_inc(v___y_1381_);
v___x_1412_ = l_Lean_Syntax_node7(v___y_1406_, v___y_1381_, v___y_1395_, v___y_1395_, v___x_1411_, v___y_1395_, v___y_1395_, v___y_1395_, v___y_1395_);
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1372_, 3);
lean_inc_ref_n(v___y_1383_, 6);
lean_inc_ref_n(v___y_1394_, 6);
v___x_1414_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1372_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1385_, 2);
v___x_1416_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1385_, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_node1(v___y_1406_, v___x_1416_, v___y_1395_);
v___x_1418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1406_);
lean_ctor_set(v___x_1418_, 1, v___x_1413_);
v___x_1419_ = l_Lean_Syntax_node2(v___y_1406_, v___y_1378_, v___y_1397_, v___y_1395_);
v___x_1420_ = l_Lean_Syntax_node1(v___y_1406_, v___y_1391_, v___x_1419_);
v___x_1421_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1422_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1372_, v___x_1421_);
lean_inc_ref(v___y_1392_);
v___x_1423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1406_);
lean_ctor_set(v___x_1423_, 1, v___y_1392_);
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_1425_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_1426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_1380_, 2);
lean_inc_n(v___y_1390_, 2);
v___x_1427_ = l_Lean_addMacroScope(v___y_1390_, v___x_1426_, v___y_1380_);
lean_inc_ref(v___y_1387_);
v___x_1428_ = l_Lean_Name_mkStr2(v___y_1387_, v___x_1424_);
lean_inc(v___y_1401_);
lean_inc(v___x_1428_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___y_1401_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_inc(v___y_1388_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___y_1388_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1406_);
lean_ctor_set(v___x_1433_, 1, v___x_1425_);
lean_ctor_set(v___x_1433_, 2, v___x_1427_);
lean_ctor_set(v___x_1433_, 3, v___x_1432_);
lean_inc(v_type_1143_);
lean_inc(v_structTy_1114_);
v___x_1434_ = l_Lean_Syntax_node2(v___y_1406_, v___y_1391_, v_structTy_1114_, v_type_1143_);
lean_inc(v___y_1375_);
v___x_1435_ = l_Lean_Syntax_node2(v___y_1406_, v___y_1375_, v___x_1433_, v___x_1434_);
v___x_1436_ = l_Lean_Syntax_node2(v___y_1406_, v___y_1393_, v___x_1423_, v___x_1435_);
v___x_1437_ = l_Lean_Syntax_node2(v___y_1406_, v___x_1422_, v___y_1395_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1439_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1372_, v___x_1438_);
lean_inc_ref(v___y_1405_);
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1406_);
lean_ctor_set(v___x_1440_, 1, v___y_1405_);
v___x_1441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1442_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1385_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1406_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_Syntax_node1(v___y_1406_, v___y_1391_, v___y_1404_);
v___x_1446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1406_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_Syntax_node3(v___y_1406_, v___x_1442_, v___x_1444_, v___x_1445_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1451_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___x_1449_, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_node2(v___y_1406_, v___x_1451_, v___y_1395_, v___y_1395_);
v_ref_1453_ = l_Lean_replaceRef(v_fields_1136_, v___y_1389_);
lean_inc(v_ref_1453_);
lean_inc(v___y_1400_);
lean_inc(v___y_1374_);
lean_inc(v___y_1407_);
v___x_1454_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1407_);
lean_ctor_set(v___x_1454_, 1, v___y_1390_);
lean_ctor_set(v___x_1454_, 2, v___y_1380_);
lean_ctor_set(v___x_1454_, 3, v___y_1374_);
lean_ctor_set(v___x_1454_, 4, v___y_1400_);
lean_ctor_set(v___x_1454_, 5, v_ref_1453_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1134_, v_ref_1453_, v___x_1454_, v___y_1399_);
lean_dec_ref(v___x_1454_);
lean_dec(v_ref_1453_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_ref_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_n(v_a_1456_, 13);
v_a_1457_ = lean_ctor_get(v___x_1455_, 1);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1455_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_1385_, 2);
lean_inc_ref_n(v___y_1383_, 5);
lean_inc_ref_n(v___y_1394_, 7);
v___x_1459_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1385_, v___x_1458_);
v___x_1460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_a_1456_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_1463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_1380_, 4);
lean_inc_n(v___y_1390_, 4);
v___x_1464_ = l_Lean_addMacroScope(v___y_1390_, v___x_1463_, v___y_1380_);
lean_inc_n(v___y_1388_, 3);
v___x_1465_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1456_);
lean_ctor_set(v___x_1465_, 1, v___x_1462_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
lean_ctor_set(v___x_1465_, 3, v___y_1388_);
v___x_1466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_1467_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1385_, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_1469_ = l_Lean_Name_mkStr4(v___y_1394_, v___y_1383_, v___y_1385_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1456_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_1473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Lean_addMacroScope(v___y_1390_, v___x_1474_, v___y_1380_);
lean_inc_ref_n(v___y_1387_, 2);
v___x_1476_ = l_Lean_Name_mkStr1(v___y_1387_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_inc_ref(v___y_1372_);
v___x_1478_ = l_Lean_Name_mkStr3(v___y_1394_, v___y_1383_, v___y_1372_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
v___x_1480_ = l_Lean_Name_mkStr2(v___y_1394_, v___y_1383_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
v___x_1482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_1483_ = l_Lean_Name_mkStr2(v___y_1394_, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = l_Lean_Name_mkStr1(v___y_1394_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___y_1388_);
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1484_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1481_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1479_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1477_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1456_);
lean_ctor_set(v___x_1492_, 1, v___x_1473_);
lean_ctor_set(v___x_1492_, 2, v___x_1475_);
lean_ctor_set(v___x_1492_, 3, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node1(v_a_1456_, v___x_1472_, v___x_1492_);
v___x_1494_ = l_Lean_Syntax_node2(v_a_1456_, v___x_1469_, v___x_1471_, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_1496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_1498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_1499_ = l_Lean_addMacroScope(v___y_1390_, v___x_1498_, v___y_1380_);
v___x_1500_ = l_Lean_Name_mkStr3(v___y_1387_, v___x_1496_, v___x_1497_);
lean_inc(v___y_1401_);
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___y_1401_);
v___x_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___y_1388_);
v___x_1503_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1456_);
lean_ctor_set(v___x_1503_, 1, v___x_1495_);
lean_ctor_set(v___x_1503_, 2, v___x_1499_);
lean_ctor_set(v___x_1503_, 3, v___x_1502_);
lean_inc(v_type_1143_);
lean_inc_n(v___y_1391_, 2);
v___x_1504_ = l_Lean_Syntax_node1(v_a_1456_, v___y_1391_, v_type_1143_);
v___x_1505_ = l_Lean_Syntax_node2(v_a_1456_, v___y_1375_, v___x_1503_, v___x_1504_);
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_a_1456_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node3(v_a_1456_, v___x_1467_, v___x_1494_, v___x_1505_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node1(v_a_1456_, v___y_1391_, v___x_1508_);
lean_inc(v___x_1459_);
v___x_1510_ = l_Lean_Syntax_node4(v_a_1456_, v___x_1459_, v_fields_1136_, v___x_1461_, v___x_1465_, v___x_1509_);
v_ref_1511_ = l_Lean_replaceRef(v___x_1510_, v___y_1389_);
lean_inc(v_ref_1511_);
lean_inc(v___y_1400_);
lean_inc(v___y_1374_);
lean_inc(v___y_1407_);
v___x_1512_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1512_, 0, v___y_1407_);
lean_ctor_set(v___x_1512_, 1, v___y_1390_);
lean_ctor_set(v___x_1512_, 2, v___y_1380_);
lean_ctor_set(v___x_1512_, 3, v___y_1374_);
lean_ctor_set(v___x_1512_, 4, v___y_1400_);
lean_ctor_set(v___x_1512_, 5, v_ref_1511_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1134_, v_ref_1511_, v___x_1512_, v_a_1457_);
lean_dec_ref(v___x_1512_);
lean_dec(v_ref_1511_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_n(v_a_1514_, 29);
v_a_1515_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1513_);
lean_inc(v___y_1395_);
lean_inc_n(v___y_1406_, 2);
v___x_1516_ = l_Lean_Syntax_node4(v___y_1406_, v___x_1439_, v___x_1440_, v___x_1448_, v___x_1452_, v___y_1395_);
v___x_1517_ = l_Lean_Syntax_node6(v___y_1406_, v___x_1414_, v___x_1417_, v___x_1418_, v___y_1395_, v___x_1420_, v___x_1437_, v___x_1516_);
lean_inc(v___y_1377_);
v___x_1518_ = l_Lean_Syntax_node2(v___y_1406_, v___y_1377_, v___x_1412_, v___x_1517_);
v___x_1519_ = lean_array_push(v___y_1376_, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1514_);
lean_ctor_set(v___x_1520_, 1, v___x_1460_);
v___x_1521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1380_, 6);
lean_inc_n(v___y_1390_, 6);
v___x_1523_ = l_Lean_addMacroScope(v___y_1390_, v___x_1522_, v___y_1380_);
lean_inc_n(v___y_1388_, 6);
v___x_1524_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1524_, 0, v_a_1514_);
lean_ctor_set(v___x_1524_, 1, v___x_1521_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
lean_ctor_set(v___x_1524_, 3, v___y_1388_);
lean_inc_ref(v___y_1408_);
v___x_1525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1514_);
lean_ctor_set(v___x_1525_, 1, v___y_1408_);
lean_inc_ref(v___y_1382_);
lean_inc_n(v___y_1391_, 6);
v___x_1526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1526_, 0, v_a_1514_);
lean_ctor_set(v___x_1526_, 1, v___y_1391_);
lean_ctor_set(v___x_1526_, 2, v___y_1382_);
v___x_1527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1529_ = l_Lean_addMacroScope(v___y_1390_, v___x_1528_, v___y_1380_);
v___x_1530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1514_);
lean_ctor_set(v___x_1530_, 1, v___x_1527_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
lean_ctor_set(v___x_1530_, 3, v___y_1388_);
lean_inc_ref_n(v___x_1526_, 13);
lean_inc_n(v___y_1373_, 2);
v___x_1531_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1373_, v___x_1530_, v___x_1526_);
lean_inc_ref(v___y_1405_);
v___x_1532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_a_1514_);
lean_ctor_set(v___x_1532_, 1, v___y_1405_);
lean_inc_ref(v___x_1532_);
lean_inc(v___y_1403_);
v___x_1533_ = l_Lean_Syntax_node3(v_a_1514_, v___y_1403_, v___x_1532_, v___x_1526_, v___y_1384_);
v___x_1534_ = l_Lean_Syntax_node3(v_a_1514_, v___y_1391_, v___x_1526_, v___x_1526_, v___x_1533_);
lean_inc(v___x_1534_);
lean_inc_n(v___y_1396_, 2);
v___x_1535_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1396_, v___x_1531_, v___x_1534_);
v___x_1536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1538_ = l_Lean_addMacroScope(v___y_1390_, v___x_1537_, v___y_1380_);
v___x_1539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1539_, 0, v_a_1514_);
lean_ctor_set(v___x_1539_, 1, v___x_1536_);
lean_ctor_set(v___x_1539_, 2, v___x_1538_);
lean_ctor_set(v___x_1539_, 3, v___y_1388_);
v___x_1540_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1373_, v___x_1539_, v___x_1526_);
v___x_1541_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1396_, v___x_1540_, v___x_1534_);
v___x_1542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_1544_ = l_Lean_addMacroScope(v___y_1390_, v___x_1543_, v___y_1380_);
v___x_1545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1514_);
lean_ctor_set(v___x_1545_, 1, v___x_1542_);
lean_ctor_set(v___x_1545_, 2, v___x_1544_);
lean_ctor_set(v___x_1545_, 3, v___y_1388_);
v___x_1546_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1373_, v___x_1545_, v___x_1526_);
v___x_1547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_1549_ = l_Lean_addMacroScope(v___y_1390_, v___x_1548_, v___y_1380_);
v___x_1550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_1401_, 2);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___y_1401_);
v___x_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___y_1388_);
v___x_1553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1514_);
lean_ctor_set(v___x_1553_, 1, v___x_1547_);
lean_ctor_set(v___x_1553_, 2, v___x_1549_);
lean_ctor_set(v___x_1553_, 3, v___x_1552_);
v___x_1554_ = l_Lean_Syntax_node3(v_a_1514_, v___y_1403_, v___x_1532_, v___x_1526_, v___x_1553_);
v___x_1555_ = l_Lean_Syntax_node3(v_a_1514_, v___y_1391_, v___x_1526_, v___x_1526_, v___x_1554_);
v___x_1556_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1396_, v___x_1546_, v___x_1555_);
v___x_1557_ = l_Lean_Syntax_node6(v_a_1514_, v___y_1391_, v___x_1535_, v___x_1526_, v___x_1541_, v___x_1526_, v___x_1556_, v___x_1526_);
v___x_1558_ = l_Lean_Syntax_node1(v_a_1514_, v___y_1398_, v___x_1557_);
v___x_1559_ = l_Lean_Syntax_node1(v_a_1514_, v___y_1379_, v___x_1526_);
lean_inc_ref(v___y_1392_);
v___x_1560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1514_);
lean_ctor_set(v___x_1560_, 1, v___y_1392_);
v___x_1561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1564_ = l_Lean_addMacroScope(v___y_1390_, v___x_1563_, v___y_1380_);
lean_inc_ref(v___y_1387_);
v___x_1565_ = l_Lean_Name_mkStr2(v___y_1387_, v___x_1561_);
lean_inc(v___x_1565_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___y_1401_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___y_1388_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1514_);
lean_ctor_set(v___x_1570_, 1, v___x_1562_);
lean_ctor_set(v___x_1570_, 2, v___x_1564_);
lean_ctor_set(v___x_1570_, 3, v___x_1569_);
v___x_1571_ = l_Lean_Syntax_node2(v_a_1514_, v___y_1391_, v___x_1560_, v___x_1570_);
lean_inc_ref(v___y_1386_);
v___x_1572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1514_);
lean_ctor_set(v___x_1572_, 1, v___y_1386_);
v___x_1573_ = l_Lean_Syntax_node6(v_a_1514_, v___y_1402_, v___x_1525_, v___x_1526_, v___x_1558_, v___x_1559_, v___x_1571_, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node1(v_a_1514_, v___y_1391_, v___x_1573_);
v___x_1575_ = l_Lean_Syntax_node4(v_a_1514_, v___x_1459_, v___x_1510_, v___x_1520_, v___x_1524_, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1519_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v_a_1125_ = v___x_1576_;
v_a_1126_ = v_a_1515_;
goto v___jp_1124_;
}
else
{
lean_object* v_a_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v___x_1510_);
lean_dec(v___x_1459_);
lean_dec(v___x_1452_);
lean_dec(v___x_1448_);
lean_dec_ref(v___x_1440_);
lean_dec(v___x_1439_);
lean_dec(v___x_1437_);
lean_dec(v___x_1420_);
lean_dec_ref(v___x_1418_);
lean_dec(v___x_1417_);
lean_dec(v___x_1414_);
lean_dec(v___x_1412_);
lean_dec(v___y_1406_);
lean_dec(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec(v___y_1398_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec(v___y_1384_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1373_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1577_ = lean_ctor_get(v___x_1513_, 0);
v_a_1578_ = lean_ctor_get(v___x_1513_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1513_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_inc(v_a_1577_);
lean_dec(v___x_1513_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v___x_1452_);
lean_dec(v___x_1448_);
lean_dec_ref(v___x_1440_);
lean_dec(v___x_1439_);
lean_dec(v___x_1437_);
lean_dec(v___x_1420_);
lean_dec_ref(v___x_1418_);
lean_dec(v___x_1417_);
lean_dec(v___x_1414_);
lean_dec(v___x_1412_);
lean_dec(v___y_1406_);
lean_dec(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec(v___y_1398_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1373_);
lean_dec(v_fields_1136_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1586_ = lean_ctor_get(v___x_1455_, 0);
v_a_1587_ = lean_ctor_get(v___x_1455_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1455_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1455_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
v___jp_1595_:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1134_, v___y_1613_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc_n(v_a_1631_, 2);
v_a_1632_ = lean_ctor_get(v___x_1630_, 1);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1630_);
v___x_1633_ = l_Lean_mkIdentFrom(v_id_1141_, v___y_1629_, v___x_1134_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1615_);
v___x_1634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1634_, 0, v_a_1631_);
lean_ctor_set(v___x_1634_, 1, v___y_1615_);
lean_ctor_set(v___x_1634_, 2, v___y_1606_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1635_; lean_object* v___x_1636_; 
v_val_1635_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1635_);
v___x_1636_ = l_Array_mkArray1___redArg(v_val_1635_);
v___y_1372_ = v___y_1596_;
v___y_1373_ = v___y_1597_;
v___y_1374_ = v___y_1598_;
v___y_1375_ = v___y_1599_;
v___y_1376_ = v___y_1600_;
v___y_1377_ = v___y_1602_;
v___y_1378_ = v___y_1601_;
v___y_1379_ = v___y_1604_;
v___y_1380_ = v___y_1603_;
v___y_1381_ = v___y_1605_;
v___y_1382_ = v___y_1606_;
v___y_1383_ = v___y_1607_;
v___y_1384_ = v___y_1608_;
v___y_1385_ = v___y_1609_;
v___y_1386_ = v___y_1610_;
v___y_1387_ = v___y_1611_;
v___y_1388_ = v___y_1612_;
v___y_1389_ = v___y_1613_;
v___y_1390_ = v___y_1614_;
v___y_1391_ = v___y_1615_;
v___y_1392_ = v___y_1616_;
v___y_1393_ = v___y_1617_;
v___y_1394_ = v___y_1618_;
v___y_1395_ = v___x_1634_;
v___y_1396_ = v___y_1619_;
v___y_1397_ = v___x_1633_;
v___y_1398_ = v___y_1620_;
v___y_1399_ = v_a_1632_;
v___y_1400_ = v___y_1621_;
v___y_1401_ = v___y_1622_;
v___y_1402_ = v___y_1624_;
v___y_1403_ = v___y_1623_;
v___y_1404_ = v___y_1625_;
v___y_1405_ = v___y_1626_;
v___y_1406_ = v_a_1631_;
v___y_1407_ = v___y_1627_;
v___y_1408_ = v___y_1628_;
v___y_1409_ = v___x_1636_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1372_ = v___y_1596_;
v___y_1373_ = v___y_1597_;
v___y_1374_ = v___y_1598_;
v___y_1375_ = v___y_1599_;
v___y_1376_ = v___y_1600_;
v___y_1377_ = v___y_1602_;
v___y_1378_ = v___y_1601_;
v___y_1379_ = v___y_1604_;
v___y_1380_ = v___y_1603_;
v___y_1381_ = v___y_1605_;
v___y_1382_ = v___y_1606_;
v___y_1383_ = v___y_1607_;
v___y_1384_ = v___y_1608_;
v___y_1385_ = v___y_1609_;
v___y_1386_ = v___y_1610_;
v___y_1387_ = v___y_1611_;
v___y_1388_ = v___y_1612_;
v___y_1389_ = v___y_1613_;
v___y_1390_ = v___y_1614_;
v___y_1391_ = v___y_1615_;
v___y_1392_ = v___y_1616_;
v___y_1393_ = v___y_1617_;
v___y_1394_ = v___y_1618_;
v___y_1395_ = v___x_1634_;
v___y_1396_ = v___y_1619_;
v___y_1397_ = v___x_1633_;
v___y_1398_ = v___y_1620_;
v___y_1399_ = v_a_1632_;
v___y_1400_ = v___y_1621_;
v___y_1401_ = v___y_1622_;
v___y_1402_ = v___y_1624_;
v___y_1403_ = v___y_1623_;
v___y_1404_ = v___y_1625_;
v___y_1405_ = v___y_1626_;
v___y_1406_ = v_a_1631_;
v___y_1407_ = v___y_1627_;
v___y_1408_ = v___y_1628_;
v___y_1409_ = v___x_1637_;
goto v___jp_1371_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___y_1629_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v___y_1604_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec(v___y_1597_);
lean_dec(v_fields_1136_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1638_ = lean_ctor_get(v___x_1630_, 0);
v_a_1639_ = lean_ctor_get(v___x_1630_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1630_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_inc(v_a_1638_);
lean_dec(v___x_1630_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
v___jp_1648_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_inc_ref_n(v___y_1660_, 2);
v___x_1666_ = l_Array_append___redArg(v___y_1660_, v___y_1665_);
lean_dec_ref(v___y_1665_);
lean_inc_n(v___y_1649_, 19);
lean_inc_n(v___y_1650_, 69);
v___x_1667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1650_);
lean_ctor_set(v___x_1667_, 1, v___y_1649_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
lean_inc_n(v___y_1659_, 35);
lean_inc(v___y_1658_);
v___x_1668_ = l_Lean_Syntax_node7(v___y_1650_, v___y_1658_, v___y_1659_, v___y_1659_, v___x_1667_, v___y_1659_, v___y_1659_, v___y_1659_, v___y_1659_);
v___x_1669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_1651_, 4);
lean_inc_ref_n(v___y_1661_, 15);
lean_inc_ref_n(v___y_1652_, 15);
v___x_1670_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___y_1651_, v___x_1669_);
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_1672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1650_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_1674_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___y_1651_, v___x_1673_);
lean_inc(v___y_1656_);
lean_inc(v___x_1674_);
v___x_1675_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1674_, v___y_1656_, v___y_1659_);
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_1677_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___y_1651_, v___x_1676_);
v___x_1678_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_1679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_1680_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_1682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___y_1650_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_1684_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1683_);
v___x_1685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_1686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_1657_, 8);
lean_inc_n(v___y_1664_, 8);
v___x_1687_ = l_Lean_addMacroScope(v___y_1664_, v___x_1686_, v___y_1657_);
v___x_1688_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_1689_ = lean_box(0);
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_1691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1650_);
lean_ctor_set(v___x_1691_, 1, v___x_1685_);
lean_ctor_set(v___x_1691_, 2, v___x_1687_);
lean_ctor_set(v___x_1691_, 3, v___x_1690_);
lean_inc(v_type_1143_);
lean_inc(v_structTy_1114_);
v___x_1692_ = l_Lean_Syntax_node2(v___y_1650_, v___y_1649_, v_structTy_1114_, v_type_1143_);
lean_inc_n(v___x_1684_, 2);
v___x_1693_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1684_, v___x_1691_, v___x_1692_);
lean_inc(v___x_1680_);
v___x_1694_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1680_, v___x_1682_, v___x_1693_);
v___x_1695_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1677_, v___y_1659_, v___x_1695_);
v___x_1697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_1698_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___y_1651_, v___x_1697_);
v___x_1699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_1700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1650_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_1702_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_1704_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1703_);
v___x_1705_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_1706_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1705_);
v___x_1707_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_1708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_1709_ = l_Lean_addMacroScope(v___y_1664_, v___x_1708_, v___y_1657_);
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_1711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1711_, 0, v___y_1650_);
lean_ctor_set(v___x_1711_, 1, v___x_1707_);
lean_ctor_set(v___x_1711_, 2, v___x_1709_);
lean_ctor_set(v___x_1711_, 3, v___x_1710_);
lean_inc_n(v___x_1706_, 5);
v___x_1712_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1706_, v___x_1711_, v___y_1659_);
v___x_1713_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_1714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_1715_ = l_Lean_addMacroScope(v___y_1664_, v___x_1714_, v___y_1657_);
v___x_1716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1716_, 0, v___y_1650_);
lean_ctor_set(v___x_1716_, 1, v___x_1713_);
lean_ctor_set(v___x_1716_, 2, v___x_1715_);
lean_ctor_set(v___x_1716_, 3, v___x_1689_);
lean_inc_ref_n(v___x_1716_, 3);
v___x_1717_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1716_);
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_1719_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_1721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1650_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_1723_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1722_);
v___x_1724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_1725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___y_1650_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
lean_inc_n(v_id_1141_, 3);
v___x_1726_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1723_, v___x_1716_, v___x_1725_, v_id_1141_);
lean_inc(v___x_1726_);
lean_inc_ref_n(v___x_1721_, 5);
lean_inc_n(v___x_1719_, 6);
v___x_1727_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1726_);
lean_inc(v___x_1717_);
v___x_1728_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___x_1717_, v___y_1659_, v___x_1727_);
lean_inc_n(v___x_1704_, 6);
v___x_1729_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1712_, v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_1731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_1732_ = l_Lean_addMacroScope(v___y_1664_, v___x_1731_, v___y_1657_);
v___x_1733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_1734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1734_, 0, v___y_1650_);
lean_ctor_set(v___x_1734_, 1, v___x_1730_);
lean_ctor_set(v___x_1734_, 2, v___x_1732_);
lean_ctor_set(v___x_1734_, 3, v___x_1733_);
v___x_1735_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1706_, v___x_1734_, v___y_1659_);
v___x_1736_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_1737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_1738_ = l_Lean_addMacroScope(v___y_1664_, v___x_1737_, v___y_1657_);
v___x_1739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1650_);
lean_ctor_set(v___x_1739_, 1, v___x_1736_);
lean_ctor_set(v___x_1739_, 2, v___x_1738_);
lean_ctor_set(v___x_1739_, 3, v___x_1689_);
lean_inc_ref(v___x_1739_);
v___x_1740_ = l_Lean_Syntax_node2(v___y_1650_, v___y_1649_, v___x_1739_, v___x_1716_);
v___x_1741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_1742_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1741_);
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_1744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___y_1650_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_1746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1650_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_Syntax_node2(v___y_1650_, v___y_1649_, v___x_1717_, v___x_1746_);
v___x_1748_ = lean_box(0);
v___x_1749_ = l_Lean_SourceInfo_fromRef(v___x_1748_, v___x_1134_);
lean_inc(v___x_1749_);
v___x_1750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___y_1649_);
lean_ctor_set(v___x_1750_, 2, v___y_1660_);
v___x_1751_ = l_Lean_Syntax_node2(v___x_1749_, v___x_1706_, v_id_1141_, v___x_1750_);
v___x_1752_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1739_);
v___x_1753_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___y_1659_, v___y_1659_, v___x_1752_);
lean_inc(v___x_1751_);
v___x_1754_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1751_, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1754_);
lean_inc_n(v___x_1702_, 3);
v___x_1756_ = l_Lean_Syntax_node1(v___y_1650_, v___x_1702_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_1758_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1757_);
lean_inc(v___x_1758_);
v___x_1759_ = l_Lean_Syntax_node1(v___y_1650_, v___x_1758_, v___y_1659_);
v___x_1760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1650_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
lean_inc_ref(v___x_1761_);
lean_inc(v___x_1759_);
lean_inc(v___x_1747_);
lean_inc_ref(v___x_1744_);
lean_inc_n(v___x_1742_, 2);
v___x_1762_ = l_Lean_Syntax_node6(v___y_1650_, v___x_1742_, v___x_1744_, v___x_1747_, v___x_1756_, v___x_1759_, v___y_1659_, v___x_1761_);
v___x_1763_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1762_);
v___x_1764_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___x_1740_, v___y_1659_, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1735_, v___x_1764_);
v___x_1766_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_1767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_1768_ = l_Lean_addMacroScope(v___y_1664_, v___x_1767_, v___y_1657_);
v___x_1769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_1770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1650_);
lean_ctor_set(v___x_1770_, 1, v___x_1766_);
lean_ctor_set(v___x_1770_, 2, v___x_1768_);
lean_ctor_set(v___x_1770_, 3, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1706_, v___x_1770_, v___y_1659_);
v___x_1772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_1773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_1774_ = l_Lean_addMacroScope(v___y_1664_, v___x_1773_, v___y_1657_);
v___x_1775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1775_, 0, v___y_1650_);
lean_ctor_set(v___x_1775_, 1, v___x_1772_);
lean_ctor_set(v___x_1775_, 2, v___x_1774_);
lean_ctor_set(v___x_1775_, 3, v___x_1689_);
lean_inc_ref(v___x_1775_);
v___x_1776_ = l_Lean_Syntax_node2(v___y_1650_, v___y_1649_, v___x_1775_, v___x_1716_);
v___x_1777_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1726_);
v___x_1778_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1684_, v___x_1775_, v___x_1777_);
v___x_1779_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1778_);
v___x_1780_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___y_1659_, v___y_1659_, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1751_, v___x_1780_);
v___x_1782_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1781_);
v___x_1783_ = l_Lean_Syntax_node1(v___y_1650_, v___x_1702_, v___x_1782_);
v___x_1784_ = l_Lean_Syntax_node6(v___y_1650_, v___x_1742_, v___x_1744_, v___x_1747_, v___x_1783_, v___x_1759_, v___y_1659_, v___x_1761_);
v___x_1785_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___x_1776_, v___y_1659_, v___x_1785_);
v___x_1787_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1771_, v___x_1786_);
v___x_1788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_1789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_1790_ = l_Lean_addMacroScope(v___y_1664_, v___x_1789_, v___y_1657_);
v___x_1791_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1791_, 0, v___y_1650_);
lean_ctor_set(v___x_1791_, 1, v___x_1788_);
lean_ctor_set(v___x_1791_, 2, v___x_1790_);
lean_ctor_set(v___x_1791_, 3, v___x_1689_);
v___x_1792_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1706_, v___x_1791_, v___y_1659_);
v___x_1793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_1794_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___y_1650_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
v___x_1796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_1797_ = l_Lean_Name_mkStr4(v___y_1652_, v___y_1661_, v___x_1678_, v___x_1796_);
lean_inc(v___x_1115_);
v___x_1798_ = l_Lean_Syntax_node1(v___y_1650_, v___y_1649_, v___x_1115_);
v___x_1799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___y_1650_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
lean_inc(v_defVal_1144_);
v___x_1801_ = l_Lean_Syntax_node4(v___y_1650_, v___x_1797_, v___x_1798_, v___y_1659_, v___x_1800_, v_defVal_1144_);
v___x_1802_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1794_, v___x_1795_, v___x_1801_);
v___x_1803_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1719_, v___x_1721_, v___y_1659_, v___x_1802_);
v___x_1804_ = l_Lean_Syntax_node3(v___y_1650_, v___y_1649_, v___y_1659_, v___y_1659_, v___x_1803_);
v___x_1805_ = l_Lean_Syntax_node2(v___y_1650_, v___x_1704_, v___x_1792_, v___x_1804_);
v___x_1806_ = l_Lean_Syntax_node7(v___y_1650_, v___y_1649_, v___x_1729_, v___y_1659_, v___x_1765_, v___y_1659_, v___x_1787_, v___y_1659_, v___x_1805_);
v___x_1807_ = l_Lean_Syntax_node1(v___y_1650_, v___x_1702_, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node3(v___y_1650_, v___x_1698_, v___x_1700_, v___x_1807_, v___y_1659_);
v___x_1809_ = l_Lean_Syntax_node5(v___y_1650_, v___x_1670_, v___x_1672_, v___x_1675_, v___x_1696_, v___x_1808_, v___y_1659_);
lean_inc(v___y_1655_);
v___x_1810_ = l_Lean_Syntax_node2(v___y_1650_, v___y_1655_, v___x_1668_, v___x_1809_);
v___x_1811_ = lean_array_push(v_cmds_1135_, v___x_1810_);
lean_inc(v___x_1647_);
v___x_1812_ = l_Lake_Name_quoteFrom(v_id_1141_, v___x_1647_, v___x_1134_);
if (v_parent_1145_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
lean_dec(v___x_1647_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_size(v_ids_1142_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v___x_1812_);
lean_dec(v___x_1758_);
lean_dec(v___x_1742_);
lean_dec(v___x_1719_);
lean_dec(v___x_1706_);
lean_dec(v___x_1704_);
lean_dec(v___x_1702_);
lean_dec(v___x_1684_);
lean_dec(v___x_1680_);
lean_dec(v___x_1674_);
lean_dec(v___y_1656_);
lean_del_object(v___x_1138_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1811_);
lean_ctor_set(v___x_1816_, 1, v_fields_1136_);
v_a_1125_ = v___x_1816_;
v_a_1126_ = v___y_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1817_ = lean_array_fget_borrowed(v_ids_1142_, v___x_1813_);
v___x_1818_ = l_Lean_TSyntax_getId(v___x_1817_);
lean_inc(v___x_1818_);
lean_inc(v___x_1817_);
v___x_1819_ = l_Lake_Name_quoteFrom(v___x_1817_, v___x_1818_, v___x_1134_);
v___x_1820_ = l_Lean_Name_hasMacroScopes(v___x_1818_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1117_, v___x_1818_);
lean_inc(v___x_1817_);
v___y_1316_ = v___x_1819_;
v___y_1317_ = v___y_1651_;
v___y_1318_ = v___x_1706_;
v___y_1319_ = v___x_1813_;
v___y_1320_ = v___y_1653_;
v___y_1321_ = v___x_1684_;
v___y_1322_ = v___x_1811_;
v___y_1323_ = v___x_1674_;
v___y_1324_ = v___y_1655_;
v___y_1325_ = v___x_1758_;
v___y_1326_ = v___y_1657_;
v___y_1327_ = v___y_1658_;
v___y_1328_ = v___y_1660_;
v___y_1329_ = v___y_1661_;
v___y_1330_ = v___x_1812_;
v___y_1331_ = v___x_1678_;
v___y_1332_ = v___x_1760_;
v___y_1333_ = v___x_1688_;
v___y_1334_ = v___x_1689_;
v___y_1335_ = v___y_1663_;
v___y_1336_ = v___y_1664_;
v___y_1337_ = v___y_1649_;
v___y_1338_ = v___x_1681_;
v___y_1339_ = v___x_1814_;
v___y_1340_ = v___x_1680_;
v___y_1341_ = v___y_1652_;
v___y_1342_ = v___x_1704_;
v___y_1343_ = v___x_1702_;
v___y_1344_ = v___y_1654_;
v___y_1345_ = v___x_1689_;
v___y_1346_ = v___x_1719_;
v___y_1347_ = v___x_1742_;
v___y_1348_ = v___y_1656_;
v___y_1349_ = v___x_1720_;
v___y_1350_ = v___x_1817_;
v___y_1351_ = v___y_1662_;
v___y_1352_ = v___x_1743_;
v___y_1353_ = v___x_1821_;
goto v___jp_1315_;
}
else
{
lean_object* v_view_1822_; lean_object* v_name_1823_; lean_object* v_imported_1824_; lean_object* v_ctx_1825_; lean_object* v_scopes_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_view_1822_ = l_Lean_extractMacroScopes(v___x_1818_);
v_name_1823_ = lean_ctor_get(v_view_1822_, 0);
v_imported_1824_ = lean_ctor_get(v_view_1822_, 1);
v_ctx_1825_ = lean_ctor_get(v_view_1822_, 2);
v_scopes_1826_ = lean_ctor_get(v_view_1822_, 3);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_view_1822_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v_view_1822_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_scopes_1826_);
lean_inc(v_ctx_1825_);
lean_inc(v_imported_1824_);
lean_inc(v_name_1823_);
lean_dec(v_view_1822_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1117_, v_name_1823_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_imported_1824_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_ctx_1825_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_scopes_1826_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_MacroScopesView_review(v___x_1832_);
lean_inc(v___x_1817_);
v___y_1316_ = v___x_1819_;
v___y_1317_ = v___y_1651_;
v___y_1318_ = v___x_1706_;
v___y_1319_ = v___x_1813_;
v___y_1320_ = v___y_1653_;
v___y_1321_ = v___x_1684_;
v___y_1322_ = v___x_1811_;
v___y_1323_ = v___x_1674_;
v___y_1324_ = v___y_1655_;
v___y_1325_ = v___x_1758_;
v___y_1326_ = v___y_1657_;
v___y_1327_ = v___y_1658_;
v___y_1328_ = v___y_1660_;
v___y_1329_ = v___y_1661_;
v___y_1330_ = v___x_1812_;
v___y_1331_ = v___x_1678_;
v___y_1332_ = v___x_1760_;
v___y_1333_ = v___x_1688_;
v___y_1334_ = v___x_1689_;
v___y_1335_ = v___y_1663_;
v___y_1336_ = v___y_1664_;
v___y_1337_ = v___y_1649_;
v___y_1338_ = v___x_1681_;
v___y_1339_ = v___x_1814_;
v___y_1340_ = v___x_1680_;
v___y_1341_ = v___y_1652_;
v___y_1342_ = v___x_1704_;
v___y_1343_ = v___x_1702_;
v___y_1344_ = v___y_1654_;
v___y_1345_ = v___x_1689_;
v___y_1346_ = v___x_1719_;
v___y_1347_ = v___x_1742_;
v___y_1348_ = v___y_1656_;
v___y_1349_ = v___x_1720_;
v___y_1350_ = v___x_1817_;
v___y_1351_ = v___y_1662_;
v___y_1352_ = v___x_1743_;
v___y_1353_ = v___x_1833_;
goto v___jp_1315_;
}
}
}
}
}
else
{
uint8_t v___x_1836_; 
lean_del_object(v___x_1138_);
v___x_1836_ = l_Lean_Name_hasMacroScopes(v___x_1647_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1117_, v___x_1647_);
v___y_1596_ = v___y_1651_;
v___y_1597_ = v___x_1706_;
v___y_1598_ = v___y_1653_;
v___y_1599_ = v___x_1684_;
v___y_1600_ = v___x_1811_;
v___y_1601_ = v___x_1674_;
v___y_1602_ = v___y_1655_;
v___y_1603_ = v___y_1657_;
v___y_1604_ = v___x_1758_;
v___y_1605_ = v___y_1658_;
v___y_1606_ = v___y_1660_;
v___y_1607_ = v___y_1661_;
v___y_1608_ = v___x_1812_;
v___y_1609_ = v___x_1678_;
v___y_1610_ = v___x_1760_;
v___y_1611_ = v___x_1688_;
v___y_1612_ = v___x_1689_;
v___y_1613_ = v___y_1663_;
v___y_1614_ = v___y_1664_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___x_1681_;
v___y_1617_ = v___x_1680_;
v___y_1618_ = v___y_1652_;
v___y_1619_ = v___x_1704_;
v___y_1620_ = v___x_1702_;
v___y_1621_ = v___y_1654_;
v___y_1622_ = v___x_1689_;
v___y_1623_ = v___x_1719_;
v___y_1624_ = v___x_1742_;
v___y_1625_ = v___y_1656_;
v___y_1626_ = v___x_1720_;
v___y_1627_ = v___y_1662_;
v___y_1628_ = v___x_1743_;
v___y_1629_ = v___x_1837_;
goto v___jp_1595_;
}
else
{
lean_object* v_view_1838_; lean_object* v_name_1839_; lean_object* v_imported_1840_; lean_object* v_ctx_1841_; lean_object* v_scopes_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v_view_1838_ = l_Lean_extractMacroScopes(v___x_1647_);
v_name_1839_ = lean_ctor_get(v_view_1838_, 0);
v_imported_1840_ = lean_ctor_get(v_view_1838_, 1);
v_ctx_1841_ = lean_ctor_get(v_view_1838_, 2);
v_scopes_1842_ = lean_ctor_get(v_view_1838_, 3);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_view_1838_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v_view_1838_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_scopes_1842_);
lean_inc(v_ctx_1841_);
lean_inc(v_imported_1840_);
lean_inc(v_name_1839_);
lean_dec(v_view_1838_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1117_, v_name_1839_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_imported_1840_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ctx_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_scopes_1842_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_MacroScopesView_review(v___x_1848_);
v___y_1596_ = v___y_1651_;
v___y_1597_ = v___x_1706_;
v___y_1598_ = v___y_1653_;
v___y_1599_ = v___x_1684_;
v___y_1600_ = v___x_1811_;
v___y_1601_ = v___x_1674_;
v___y_1602_ = v___y_1655_;
v___y_1603_ = v___y_1657_;
v___y_1604_ = v___x_1758_;
v___y_1605_ = v___y_1658_;
v___y_1606_ = v___y_1660_;
v___y_1607_ = v___y_1661_;
v___y_1608_ = v___x_1812_;
v___y_1609_ = v___x_1678_;
v___y_1610_ = v___x_1760_;
v___y_1611_ = v___x_1688_;
v___y_1612_ = v___x_1689_;
v___y_1613_ = v___y_1663_;
v___y_1614_ = v___y_1664_;
v___y_1615_ = v___y_1649_;
v___y_1616_ = v___x_1681_;
v___y_1617_ = v___x_1680_;
v___y_1618_ = v___y_1652_;
v___y_1619_ = v___x_1704_;
v___y_1620_ = v___x_1702_;
v___y_1621_ = v___y_1654_;
v___y_1622_ = v___x_1689_;
v___y_1623_ = v___x_1719_;
v___y_1624_ = v___x_1742_;
v___y_1625_ = v___y_1656_;
v___y_1626_ = v___x_1720_;
v___y_1627_ = v___y_1662_;
v___y_1628_ = v___x_1743_;
v___y_1629_ = v___x_1849_;
goto v___jp_1595_;
}
}
}
}
}
v___jp_1852_:
{
lean_object* v_methods_1854_; lean_object* v_quotContext_1855_; lean_object* v_currMacroScope_1856_; lean_object* v_currRecDepth_1857_; lean_object* v_maxRecDepth_1858_; lean_object* v_ref_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_methods_1854_ = lean_ctor_get(v___y_1122_, 0);
v_quotContext_1855_ = lean_ctor_get(v___y_1122_, 1);
v_currMacroScope_1856_ = lean_ctor_get(v___y_1122_, 2);
v_currRecDepth_1857_ = lean_ctor_get(v___y_1122_, 3);
v_maxRecDepth_1858_ = lean_ctor_get(v___y_1122_, 4);
v_ref_1859_ = lean_ctor_get(v___y_1122_, 5);
v___x_1860_ = l_Lean_mkIdentFrom(v_id_1141_, v___y_1853_, v___x_1134_);
v___x_1861_ = l_Lean_SourceInfo_fromRef(v_ref_1859_, v___x_1134_);
v___x_1862_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_1863_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_1864_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_1865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_1866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_1867_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_1868_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_1861_);
v___x_1869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1861_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
lean_ctor_set(v___x_1869_, 2, v___x_1868_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1871_; 
v_val_1870_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1870_);
v___x_1871_ = l_Array_mkArray1___redArg(v_val_1870_);
v___y_1649_ = v___x_1867_;
v___y_1650_ = v___x_1861_;
v___y_1651_ = v___x_1864_;
v___y_1652_ = v___x_1862_;
v___y_1653_ = v_currRecDepth_1857_;
v___y_1654_ = v_maxRecDepth_1858_;
v___y_1655_ = v___x_1865_;
v___y_1656_ = v___x_1860_;
v___y_1657_ = v_currMacroScope_1856_;
v___y_1658_ = v___x_1866_;
v___y_1659_ = v___x_1869_;
v___y_1660_ = v___x_1868_;
v___y_1661_ = v___x_1863_;
v___y_1662_ = v_methods_1854_;
v___y_1663_ = v_ref_1859_;
v___y_1664_ = v_quotContext_1855_;
v___y_1665_ = v___x_1871_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1649_ = v___x_1867_;
v___y_1650_ = v___x_1861_;
v___y_1651_ = v___x_1864_;
v___y_1652_ = v___x_1862_;
v___y_1653_ = v_currRecDepth_1857_;
v___y_1654_ = v_maxRecDepth_1858_;
v___y_1655_ = v___x_1865_;
v___y_1656_ = v___x_1860_;
v___y_1657_ = v_currMacroScope_1856_;
v___y_1658_ = v___x_1866_;
v___y_1659_ = v___x_1869_;
v___y_1660_ = v___x_1868_;
v___y_1661_ = v___x_1863_;
v___y_1662_ = v_methods_1854_;
v___y_1663_ = v_ref_1859_;
v___y_1664_ = v_quotContext_1855_;
v___y_1665_ = v___x_1872_;
goto v___jp_1648_;
}
}
}
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_b_1121_);
lean_ctor_set(v___x_1890_, 1, v___y_1123_);
return v___x_1890_;
}
v___jp_1124_:
{
size_t v___x_1127_; size_t v___x_1128_; 
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1119_, v___x_1127_);
v_i_1119_ = v___x_1128_;
v_b_1121_ = v_a_1125_;
v___y_1123_ = v_a_1126_;
goto _start;
}
v___jp_1130_:
{
if (lean_obj_tag(v___y_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_a_1133_; 
v_a_1132_ = lean_ctor_get(v___y_1131_, 0);
lean_inc(v_a_1132_);
v_a_1133_ = lean_ctor_get(v___y_1131_, 1);
lean_inc(v_a_1133_);
lean_dec_ref(v___y_1131_);
v_a_1125_ = v_a_1132_;
v_a_1126_ = v_a_1133_;
goto v___jp_1124_;
}
else
{
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
return v___y_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___boxed(lean_object* v_structTy_1891_, lean_object* v___x_1892_, lean_object* v_vis_x3f_1893_, lean_object* v_structId_1894_, lean_object* v_as_1895_, lean_object* v_i_1896_, lean_object* v_stop_1897_, lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
size_t v_i_boxed_1901_; size_t v_stop_boxed_1902_; lean_object* v_res_1903_; 
v_i_boxed_1901_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_stop_boxed_1902_ = lean_unbox_usize(v_stop_1897_);
lean_dec(v_stop_1897_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1891_, v___x_1892_, v_vis_x3f_1893_, v_structId_1894_, v_as_1895_, v_i_boxed_1901_, v_stop_boxed_1902_, v_b_1898_, v___y_1899_, v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v_as_1895_);
lean_dec(v_structId_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(lean_object* v_structTy_1904_, lean_object* v___x_1905_, lean_object* v_vis_x3f_1906_, lean_object* v_structId_1907_, lean_object* v_as_1908_, size_t v_i_1909_, size_t v_stop_1910_, lean_object* v_b_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v___y_1921_; uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_eq(v_i_1909_, v_stop_1910_);
if (v___x_1924_ == 0)
{
lean_object* v_cmds_1925_; lean_object* v_fields_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_2679_; 
v_cmds_1925_ = lean_ctor_get(v_b_1911_, 0);
v_fields_1926_ = lean_ctor_get(v_b_1911_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_b_1911_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_1928_ = v_b_1911_;
v_isShared_1929_ = v_isSharedCheck_2679_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_fields_1926_);
lean_inc(v_cmds_1925_);
lean_dec(v_b_1911_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_2679_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v_id_1931_; lean_object* v_ids_1932_; lean_object* v_type_1933_; lean_object* v_defVal_1934_; uint8_t v_parent_1935_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___x_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2643_; uint8_t v___x_2663_; 
v___x_1930_ = lean_array_uget_borrowed(v_as_1908_, v_i_1909_);
v_id_1931_ = lean_ctor_get(v___x_1930_, 2);
v_ids_1932_ = lean_ctor_get(v___x_1930_, 3);
v_type_1933_ = lean_ctor_get(v___x_1930_, 4);
v_defVal_1934_ = lean_ctor_get(v___x_1930_, 5);
v_parent_1935_ = lean_ctor_get_uint8(v___x_1930_, sizeof(void*)*7);
v___x_2437_ = l_Lean_TSyntax_getId(v_id_1931_);
v___x_2663_ = l_Lean_Name_hasMacroScopes(v___x_2437_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_inc(v___x_2437_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1907_, v___x_2437_);
v___y_2643_ = v___x_2664_;
goto v___jp_2642_;
}
else
{
lean_object* v_view_2665_; lean_object* v_name_2666_; lean_object* v_imported_2667_; lean_object* v_ctx_2668_; lean_object* v_scopes_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2678_; 
lean_inc(v___x_2437_);
v_view_2665_ = l_Lean_extractMacroScopes(v___x_2437_);
v_name_2666_ = lean_ctor_get(v_view_2665_, 0);
v_imported_2667_ = lean_ctor_get(v_view_2665_, 1);
v_ctx_2668_ = lean_ctor_get(v_view_2665_, 2);
v_scopes_2669_ = lean_ctor_get(v_view_2665_, 3);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_view_2665_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2671_ = v_view_2665_;
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_scopes_2669_);
lean_inc(v_ctx_2668_);
lean_inc(v_imported_2667_);
lean_inc(v_name_2666_);
lean_dec(v_view_2665_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1907_, v_name_2666_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_imported_2667_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_ctx_2668_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_scopes_2669_);
v___x_2675_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_MacroScopesView_review(v___x_2675_);
v___y_2643_ = v___x_2676_;
goto v___jp_2642_;
}
}
}
v___jp_1936_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_ref_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc_ref(v___y_1950_);
v___x_1977_ = l_Array_append___redArg(v___y_1950_, v___y_1976_);
lean_dec_ref(v___y_1976_);
lean_inc_n(v___y_1949_, 4);
lean_inc_n(v___y_1952_, 18);
v___x_1978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1978_, 0, v___y_1952_);
lean_ctor_set(v___x_1978_, 1, v___y_1949_);
lean_ctor_set(v___x_1978_, 2, v___x_1977_);
lean_inc_n(v___y_1948_, 11);
lean_inc(v___y_1946_);
v___x_1979_ = l_Lean_Syntax_node7(v___y_1952_, v___y_1946_, v___y_1948_, v___y_1948_, v___x_1978_, v___y_1948_, v___y_1948_, v___y_1948_, v___y_1948_);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1945_, 3);
lean_inc_ref_n(v___y_1966_, 6);
lean_inc_ref_n(v___y_1961_, 6);
v___x_1981_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1945_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1947_, 2);
v___x_1983_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1947_, v___x_1982_);
v___x_1984_ = l_Lean_Syntax_node1(v___y_1952_, v___x_1983_, v___y_1948_);
v___x_1985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___y_1952_);
lean_ctor_set(v___x_1985_, 1, v___x_1980_);
v___x_1986_ = l_Lean_Syntax_node2(v___y_1952_, v___y_1953_, v___y_1969_, v___y_1948_);
v___x_1987_ = l_Lean_Syntax_node1(v___y_1952_, v___y_1949_, v___x_1986_);
v___x_1988_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1989_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1945_, v___x_1988_);
lean_inc_ref(v___y_1956_);
v___x_1990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1952_);
lean_ctor_set(v___x_1990_, 1, v___y_1956_);
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1943_, 2);
lean_inc_n(v___y_1944_, 2);
v___x_1994_ = l_Lean_addMacroScope(v___y_1944_, v___x_1993_, v___y_1943_);
lean_inc_ref(v___y_1959_);
v___x_1995_ = l_Lean_Name_mkStr2(v___y_1959_, v___x_1991_);
lean_inc(v___y_1973_);
lean_inc(v___x_1995_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v___y_1973_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_inc(v___y_1965_);
v___x_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___y_1965_);
v___x_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1996_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2000_, 0, v___y_1952_);
lean_ctor_set(v___x_2000_, 1, v___x_1992_);
lean_ctor_set(v___x_2000_, 2, v___x_1994_);
lean_ctor_set(v___x_2000_, 3, v___x_1999_);
lean_inc(v_type_1933_);
lean_inc(v___y_1958_);
lean_inc(v_structTy_1904_);
v___x_2001_ = l_Lean_Syntax_node3(v___y_1952_, v___y_1949_, v_structTy_1904_, v___y_1958_, v_type_1933_);
v___x_2002_ = l_Lean_Syntax_node2(v___y_1952_, v___y_1967_, v___x_2000_, v___x_2001_);
v___x_2003_ = l_Lean_Syntax_node2(v___y_1952_, v___y_1938_, v___x_1990_, v___x_2002_);
v___x_2004_ = l_Lean_Syntax_node2(v___y_1952_, v___x_1989_, v___y_1948_, v___x_2003_);
v___x_2005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_2006_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1945_, v___x_2005_);
lean_inc_ref(v___y_1970_);
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_1952_);
lean_ctor_set(v___x_2007_, 1, v___y_1970_);
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2009_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1947_, v___x_2008_);
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___y_1952_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
lean_inc(v___y_1975_);
v___x_2012_ = l_Lean_Syntax_node1(v___y_1952_, v___y_1949_, v___y_1975_);
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___y_1952_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_Syntax_node3(v___y_1952_, v___x_2009_, v___x_2011_, v___x_2012_, v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2018_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___x_2016_, v___x_2017_);
v___x_2019_ = l_Lean_Syntax_node2(v___y_1952_, v___x_2018_, v___y_1948_, v___y_1948_);
v_ref_2020_ = l_Lean_replaceRef(v_fields_1926_, v___y_1954_);
lean_inc(v_ref_2020_);
lean_inc(v___y_1963_);
lean_inc(v___y_1955_);
lean_inc(v___y_1940_);
v___x_2021_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2021_, 0, v___y_1940_);
lean_ctor_set(v___x_2021_, 1, v___y_1944_);
lean_ctor_set(v___x_2021_, 2, v___y_1943_);
lean_ctor_set(v___x_2021_, 3, v___y_1955_);
lean_ctor_set(v___x_2021_, 4, v___y_1963_);
lean_ctor_set(v___x_2021_, 5, v_ref_2020_);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1924_, v_ref_2020_, v___x_2021_, v___y_1957_);
lean_dec_ref(v___x_2021_);
lean_dec(v_ref_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc_n(v_a_2023_, 30);
v_a_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2022_);
lean_inc(v___y_1948_);
lean_inc_n(v___y_1952_, 2);
v___x_2025_ = l_Lean_Syntax_node4(v___y_1952_, v___x_2006_, v___x_2007_, v___x_2015_, v___x_2019_, v___y_1948_);
v___x_2026_ = l_Lean_Syntax_node6(v___y_1952_, v___x_1981_, v___x_1984_, v___x_1985_, v___y_1948_, v___x_1987_, v___x_2004_, v___x_2025_);
lean_inc(v___y_1964_);
v___x_2027_ = l_Lean_Syntax_node2(v___y_1952_, v___y_1964_, v___x_1979_, v___x_2026_);
v___x_2028_ = lean_array_push(v___y_1942_, v___x_2027_);
v___x_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1966_);
lean_inc_ref(v___y_1961_);
v___x_2030_ = l_Lean_Name_mkStr4(v___y_1961_, v___y_1966_, v___y_1947_, v___x_2029_);
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_a_2023_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1943_, 5);
lean_inc_n(v___y_1944_, 5);
v___x_2035_ = l_Lean_addMacroScope(v___y_1944_, v___x_2034_, v___y_1943_);
lean_inc_n(v___y_1965_, 5);
v___x_2036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2023_);
lean_ctor_set(v___x_2036_, 1, v___x_2033_);
lean_ctor_set(v___x_2036_, 2, v___x_2035_);
lean_ctor_set(v___x_2036_, 3, v___y_1965_);
lean_inc_ref(v___y_1951_);
v___x_2037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_a_2023_);
lean_ctor_set(v___x_2037_, 1, v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc_n(v___y_1949_, 7);
v___x_2038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2038_, 0, v_a_2023_);
lean_ctor_set(v___x_2038_, 1, v___y_1949_);
lean_ctor_set(v___x_2038_, 2, v___y_1950_);
v___x_2039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2041_ = l_Lean_addMacroScope(v___y_1944_, v___x_2040_, v___y_1943_);
v___x_2042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2023_);
lean_ctor_set(v___x_2042_, 1, v___x_2039_);
lean_ctor_set(v___x_2042_, 2, v___x_2041_);
lean_ctor_set(v___x_2042_, 3, v___y_1965_);
lean_inc_ref_n(v___x_2038_, 16);
lean_inc_n(v___y_1937_, 2);
v___x_2043_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1937_, v___x_2042_, v___x_2038_);
lean_inc_ref(v___y_1970_);
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_a_2023_);
lean_ctor_set(v___x_2044_, 1, v___y_1970_);
lean_inc_ref_n(v___x_2044_, 2);
lean_inc_n(v___y_1974_, 2);
v___x_2045_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1974_, v___x_2044_, v___x_2038_, v___y_1958_);
v___x_2046_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1949_, v___x_2038_, v___x_2038_, v___x_2045_);
lean_inc_n(v___y_1968_, 2);
v___x_2047_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1968_, v___x_2043_, v___x_2046_);
v___x_2048_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2050_ = l_Lean_addMacroScope(v___y_1944_, v___x_2049_, v___y_1943_);
v___x_2051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2023_);
lean_ctor_set(v___x_2051_, 1, v___x_2048_);
lean_ctor_set(v___x_2051_, 2, v___x_2050_);
lean_ctor_set(v___x_2051_, 3, v___y_1965_);
v___x_2052_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1937_, v___x_2051_, v___x_2038_);
lean_inc(v___y_1941_);
v___x_2053_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1974_, v___x_2044_, v___x_2038_, v___y_1941_);
v___x_2054_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1949_, v___x_2038_, v___x_2038_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1968_, v___x_2052_, v___x_2054_);
v___x_2056_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_2058_ = l_Lean_addMacroScope(v___y_1944_, v___x_2057_, v___y_1943_);
v___x_2059_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2023_);
lean_ctor_set(v___x_2059_, 1, v___x_2056_);
lean_ctor_set(v___x_2059_, 2, v___x_2058_);
lean_ctor_set(v___x_2059_, 3, v___y_1965_);
v___x_2060_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1937_, v___x_2059_, v___x_2038_);
v___x_2061_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_2062_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1974_, v___x_2044_, v___x_2038_, v___x_2061_);
v___x_2063_ = l_Lean_Syntax_node3(v_a_2023_, v___y_1949_, v___x_2038_, v___x_2038_, v___x_2062_);
v___x_2064_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1968_, v___x_2060_, v___x_2063_);
v___x_2065_ = l_Lean_Syntax_node6(v_a_2023_, v___y_1949_, v___x_2047_, v___x_2038_, v___x_2055_, v___x_2038_, v___x_2064_, v___x_2038_);
v___x_2066_ = l_Lean_Syntax_node1(v_a_2023_, v___y_1971_, v___x_2065_);
v___x_2067_ = l_Lean_Syntax_node1(v_a_2023_, v___y_1962_, v___x_2038_);
lean_inc_ref(v___y_1956_);
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_a_2023_);
lean_ctor_set(v___x_2068_, 1, v___y_1956_);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2070_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2072_ = l_Lean_addMacroScope(v___y_1944_, v___x_2071_, v___y_1943_);
lean_inc_ref(v___y_1959_);
v___x_2073_ = l_Lean_Name_mkStr2(v___y_1959_, v___x_2069_);
lean_inc(v___y_1973_);
lean_inc(v___x_2073_);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v___y_1973_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___y_1965_);
v___x_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2074_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2023_);
lean_ctor_set(v___x_2078_, 1, v___x_2070_);
lean_ctor_set(v___x_2078_, 2, v___x_2072_);
lean_ctor_set(v___x_2078_, 3, v___x_2077_);
v___x_2079_ = l_Lean_Syntax_node2(v_a_2023_, v___y_1949_, v___x_2068_, v___x_2078_);
lean_inc_ref(v___y_1939_);
v___x_2080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_a_2023_);
lean_ctor_set(v___x_2080_, 1, v___y_1939_);
v___x_2081_ = l_Lean_Syntax_node6(v_a_2023_, v___y_1972_, v___x_2037_, v___x_2038_, v___x_2066_, v___x_2067_, v___x_2079_, v___x_2080_);
v___x_2082_ = l_Lean_Syntax_node1(v_a_2023_, v___y_1949_, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_node4(v_a_2023_, v___x_2030_, v_fields_1926_, v___x_2032_, v___x_2036_, v___x_2082_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_2083_);
lean_ctor_set(v___x_1928_, 0, v___x_2028_);
v___x_2085_ = v___x_1928_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_dec_lt(v___x_2086_, v___y_1960_);
if (v___x_2087_ == 0)
{
lean_dec(v___y_1975_);
lean_dec(v___y_1960_);
lean_dec(v___y_1941_);
v_a_1915_ = v___x_2085_;
v_a_1916_ = v_a_2024_;
goto v___jp_1914_;
}
else
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_nat_dec_le(v___y_1960_, v___y_1960_);
if (v___x_2088_ == 0)
{
if (v___x_2087_ == 0)
{
lean_dec(v___y_1975_);
lean_dec(v___y_1960_);
lean_dec(v___y_1941_);
v_a_1915_ = v___x_2085_;
v_a_1916_ = v_a_2024_;
goto v___jp_1914_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_of_nat(v___y_1960_);
lean_dec(v___y_1960_);
lean_inc(v_vis_x3f_1906_);
lean_inc(v_type_1933_);
lean_inc(v_structTy_1904_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1904_, v_type_1933_, v___y_1975_, v___y_1941_, v_vis_x3f_1906_, v_structId_1907_, v_ids_1932_, v___x_2089_, v___x_2090_, v___x_2085_, v___y_1912_, v_a_2024_);
v___y_1921_ = v___x_2091_;
goto v___jp_1920_;
}
}
else
{
size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_of_nat(v___y_1960_);
lean_dec(v___y_1960_);
lean_inc(v_vis_x3f_1906_);
lean_inc(v_type_1933_);
lean_inc(v_structTy_1904_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1904_, v_type_1933_, v___y_1975_, v___y_1941_, v_vis_x3f_1906_, v_structId_1907_, v_ids_1932_, v___x_2092_, v___x_2093_, v___x_2085_, v___y_1912_, v_a_2024_);
v___y_1921_ = v___x_2094_;
goto v___jp_1920_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v___x_2019_);
lean_dec(v___x_2015_);
lean_dec_ref(v___x_2007_);
lean_dec(v___x_2006_);
lean_dec(v___x_2004_);
lean_dec(v___x_1987_);
lean_dec_ref(v___x_1985_);
lean_dec(v___x_1984_);
lean_dec(v___x_1981_);
lean_dec(v___x_1979_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1968_);
lean_dec(v___y_1962_);
lean_dec(v___y_1960_);
lean_dec(v___y_1958_);
lean_dec(v___y_1952_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1937_);
lean_del_object(v___x_1928_);
lean_dec(v_fields_1926_);
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v_a_2096_ = lean_ctor_get(v___x_2022_, 0);
v_a_2097_ = lean_ctor_get(v___x_2022_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2022_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_inc(v_a_2096_);
lean_dec(v___x_2022_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2096_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
v___jp_2105_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1924_, v___y_2122_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc_n(v_a_2145_, 2);
v_a_2146_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2144_);
v___x_2147_ = l_Lean_mkIdentFrom(v___y_2115_, v___y_2143_, v___x_1924_);
lean_dec(v___y_2115_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2119_);
v___x_2148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2145_);
lean_ctor_set(v___x_2148_, 1, v___y_2119_);
lean_ctor_set(v___x_2148_, 2, v___y_2118_);
if (lean_obj_tag(v_vis_x3f_1906_) == 1)
{
lean_object* v_val_2149_; lean_object* v___x_2150_; 
v_val_2149_ = lean_ctor_get(v_vis_x3f_1906_, 0);
lean_inc(v_val_2149_);
v___x_2150_ = l_Array_mkArray1___redArg(v_val_2149_);
v___y_1937_ = v___y_2106_;
v___y_1938_ = v___y_2107_;
v___y_1939_ = v___y_2109_;
v___y_1940_ = v___y_2108_;
v___y_1941_ = v___y_2110_;
v___y_1942_ = v___y_2112_;
v___y_1943_ = v___y_2111_;
v___y_1944_ = v___y_2114_;
v___y_1945_ = v___y_2113_;
v___y_1946_ = v___y_2116_;
v___y_1947_ = v___y_2117_;
v___y_1948_ = v___x_2148_;
v___y_1949_ = v___y_2119_;
v___y_1950_ = v___y_2118_;
v___y_1951_ = v___y_2120_;
v___y_1952_ = v_a_2145_;
v___y_1953_ = v___y_2121_;
v___y_1954_ = v___y_2122_;
v___y_1955_ = v___y_2123_;
v___y_1956_ = v___y_2124_;
v___y_1957_ = v_a_2146_;
v___y_1958_ = v___y_2125_;
v___y_1959_ = v___y_2126_;
v___y_1960_ = v___y_2127_;
v___y_1961_ = v___y_2128_;
v___y_1962_ = v___y_2129_;
v___y_1963_ = v___y_2130_;
v___y_1964_ = v___y_2131_;
v___y_1965_ = v___y_2133_;
v___y_1966_ = v___y_2135_;
v___y_1967_ = v___y_2134_;
v___y_1968_ = v___y_2136_;
v___y_1969_ = v___x_2147_;
v___y_1970_ = v___y_2137_;
v___y_1971_ = v___y_2138_;
v___y_1972_ = v___y_2139_;
v___y_1973_ = v___y_2140_;
v___y_1974_ = v___y_2142_;
v___y_1975_ = v___y_2141_;
v___y_1976_ = v___x_2150_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_mk_empty_array_with_capacity(v___y_2132_);
v___y_1937_ = v___y_2106_;
v___y_1938_ = v___y_2107_;
v___y_1939_ = v___y_2109_;
v___y_1940_ = v___y_2108_;
v___y_1941_ = v___y_2110_;
v___y_1942_ = v___y_2112_;
v___y_1943_ = v___y_2111_;
v___y_1944_ = v___y_2114_;
v___y_1945_ = v___y_2113_;
v___y_1946_ = v___y_2116_;
v___y_1947_ = v___y_2117_;
v___y_1948_ = v___x_2148_;
v___y_1949_ = v___y_2119_;
v___y_1950_ = v___y_2118_;
v___y_1951_ = v___y_2120_;
v___y_1952_ = v_a_2145_;
v___y_1953_ = v___y_2121_;
v___y_1954_ = v___y_2122_;
v___y_1955_ = v___y_2123_;
v___y_1956_ = v___y_2124_;
v___y_1957_ = v_a_2146_;
v___y_1958_ = v___y_2125_;
v___y_1959_ = v___y_2126_;
v___y_1960_ = v___y_2127_;
v___y_1961_ = v___y_2128_;
v___y_1962_ = v___y_2129_;
v___y_1963_ = v___y_2130_;
v___y_1964_ = v___y_2131_;
v___y_1965_ = v___y_2133_;
v___y_1966_ = v___y_2135_;
v___y_1967_ = v___y_2134_;
v___y_1968_ = v___y_2136_;
v___y_1969_ = v___x_2147_;
v___y_1970_ = v___y_2137_;
v___y_1971_ = v___y_2138_;
v___y_1972_ = v___y_2139_;
v___y_1973_ = v___y_2140_;
v___y_1974_ = v___y_2142_;
v___y_1975_ = v___y_2141_;
v___y_1976_ = v___x_2151_;
goto v___jp_1936_;
}
}
else
{
lean_object* v_a_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec(v___y_2136_);
lean_dec(v___y_2134_);
lean_dec(v___y_2129_);
lean_dec(v___y_2127_);
lean_dec(v___y_2125_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2110_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_del_object(v___x_1928_);
lean_dec(v_fields_1926_);
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v_a_2152_ = lean_ctor_get(v___x_2144_, 0);
v_a_2153_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_inc(v_a_2152_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
v___jp_2161_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_ref_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_inc_ref(v___y_2175_);
v___x_2200_ = l_Array_append___redArg(v___y_2175_, v___y_2199_);
lean_dec_ref(v___y_2199_);
lean_inc_n(v___y_2174_, 4);
lean_inc_n(v___y_2187_, 18);
v___x_2201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___y_2187_);
lean_ctor_set(v___x_2201_, 1, v___y_2174_);
lean_ctor_set(v___x_2201_, 2, v___x_2200_);
lean_inc_n(v___y_2178_, 11);
lean_inc(v___y_2172_);
v___x_2202_ = l_Lean_Syntax_node7(v___y_2187_, v___y_2172_, v___y_2178_, v___y_2178_, v___x_2201_, v___y_2178_, v___y_2178_, v___y_2178_, v___y_2178_);
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_2171_, 3);
lean_inc_ref_n(v___y_2190_, 6);
lean_inc_ref_n(v___y_2183_, 6);
v___x_2204_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2171_, v___x_2203_);
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_2173_, 2);
v___x_2206_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2173_, v___x_2205_);
v___x_2207_ = l_Lean_Syntax_node1(v___y_2187_, v___x_2206_, v___y_2178_);
v___x_2208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2187_);
lean_ctor_set(v___x_2208_, 1, v___x_2203_);
v___x_2209_ = l_Lean_Syntax_node2(v___y_2187_, v___y_2177_, v___y_2189_, v___y_2178_);
v___x_2210_ = l_Lean_Syntax_node1(v___y_2187_, v___y_2174_, v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_2212_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2171_, v___x_2211_);
lean_inc_ref(v___y_2181_);
v___x_2213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___y_2187_);
lean_ctor_set(v___x_2213_, 1, v___y_2181_);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_2215_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_2169_, 2);
lean_inc_n(v___y_2170_, 2);
v___x_2217_ = l_Lean_addMacroScope(v___y_2170_, v___x_2216_, v___y_2169_);
lean_inc_ref(v___y_2182_);
v___x_2218_ = l_Lean_Name_mkStr2(v___y_2182_, v___x_2214_);
lean_inc(v___y_2196_);
lean_inc(v___x_2218_);
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___y_2196_);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_inc(v___y_2188_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___y_2188_);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2223_, 0, v___y_2187_);
lean_ctor_set(v___x_2223_, 1, v___x_2215_);
lean_ctor_set(v___x_2223_, 2, v___x_2217_);
lean_ctor_set(v___x_2223_, 3, v___x_2222_);
lean_inc(v_type_1933_);
lean_inc(v_structTy_1904_);
v___x_2224_ = l_Lean_Syntax_node2(v___y_2187_, v___y_2174_, v_structTy_1904_, v_type_1933_);
lean_inc(v___y_2191_);
v___x_2225_ = l_Lean_Syntax_node2(v___y_2187_, v___y_2191_, v___x_2223_, v___x_2224_);
v___x_2226_ = l_Lean_Syntax_node2(v___y_2187_, v___y_2164_, v___x_2213_, v___x_2225_);
v___x_2227_ = l_Lean_Syntax_node2(v___y_2187_, v___x_2212_, v___y_2178_, v___x_2226_);
v___x_2228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_2229_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2171_, v___x_2228_);
lean_inc_ref(v___y_2193_);
v___x_2230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___y_2187_);
lean_ctor_set(v___x_2230_, 1, v___y_2193_);
v___x_2231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2232_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2173_, v___x_2231_);
v___x_2233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___y_2187_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_node1(v___y_2187_, v___y_2174_, v___y_2198_);
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___y_2187_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_Syntax_node3(v___y_2187_, v___x_2232_, v___x_2234_, v___x_2235_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2241_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___x_2239_, v___x_2240_);
v___x_2242_ = l_Lean_Syntax_node2(v___y_2187_, v___x_2241_, v___y_2178_, v___y_2178_);
v_ref_2243_ = l_Lean_replaceRef(v_fields_1926_, v___y_2179_);
lean_inc(v_ref_2243_);
lean_inc(v___y_2185_);
lean_inc(v___y_2180_);
lean_inc(v___y_2166_);
v___x_2244_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2244_, 0, v___y_2166_);
lean_ctor_set(v___x_2244_, 1, v___y_2170_);
lean_ctor_set(v___x_2244_, 2, v___y_2169_);
lean_ctor_set(v___x_2244_, 3, v___y_2180_);
lean_ctor_set(v___x_2244_, 4, v___y_2185_);
lean_ctor_set(v___x_2244_, 5, v_ref_2243_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1924_, v_ref_2243_, v___x_2244_, v___y_2163_);
lean_dec_ref(v___x_2244_);
lean_dec(v_ref_2243_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v_a_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v_ref_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_n(v_a_2246_, 13);
v_a_2247_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2245_);
v___x_2248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_2173_, 2);
lean_inc_ref_n(v___y_2190_, 5);
lean_inc_ref_n(v___y_2183_, 7);
v___x_2249_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2173_, v___x_2248_);
v___x_2250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_a_2246_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_2169_, 4);
lean_inc_n(v___y_2170_, 4);
v___x_2254_ = l_Lean_addMacroScope(v___y_2170_, v___x_2253_, v___y_2169_);
lean_inc_n(v___y_2188_, 3);
v___x_2255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2255_, 0, v_a_2246_);
lean_ctor_set(v___x_2255_, 1, v___x_2252_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
lean_ctor_set(v___x_2255_, 3, v___y_2188_);
v___x_2256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_2257_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2173_, v___x_2256_);
v___x_2258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_2259_ = l_Lean_Name_mkStr4(v___y_2183_, v___y_2190_, v___y_2173_, v___x_2258_);
v___x_2260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_2261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2246_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_2263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_2264_ = lean_box(0);
v___x_2265_ = l_Lean_addMacroScope(v___y_2170_, v___x_2264_, v___y_2169_);
lean_inc_ref_n(v___y_2182_, 2);
v___x_2266_ = l_Lean_Name_mkStr1(v___y_2182_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_inc_ref(v___y_2171_);
v___x_2268_ = l_Lean_Name_mkStr3(v___y_2183_, v___y_2190_, v___y_2171_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
v___x_2270_ = l_Lean_Name_mkStr2(v___y_2183_, v___y_2190_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_2273_ = l_Lean_Name_mkStr2(v___y_2183_, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = l_Lean_Name_mkStr1(v___y_2183_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___y_2188_);
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2274_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2271_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2269_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2267_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2246_);
lean_ctor_set(v___x_2282_, 1, v___x_2263_);
lean_ctor_set(v___x_2282_, 2, v___x_2265_);
lean_ctor_set(v___x_2282_, 3, v___x_2281_);
v___x_2283_ = l_Lean_Syntax_node1(v_a_2246_, v___x_2262_, v___x_2282_);
v___x_2284_ = l_Lean_Syntax_node2(v_a_2246_, v___x_2259_, v___x_2261_, v___x_2283_);
v___x_2285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_2289_ = l_Lean_addMacroScope(v___y_2170_, v___x_2288_, v___y_2169_);
v___x_2290_ = l_Lean_Name_mkStr3(v___y_2182_, v___x_2286_, v___x_2287_);
lean_inc(v___y_2196_);
v___x_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___y_2196_);
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___y_2188_);
v___x_2293_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2293_, 0, v_a_2246_);
lean_ctor_set(v___x_2293_, 1, v___x_2285_);
lean_ctor_set(v___x_2293_, 2, v___x_2289_);
lean_ctor_set(v___x_2293_, 3, v___x_2292_);
lean_inc(v_type_1933_);
lean_inc_n(v___y_2174_, 2);
v___x_2294_ = l_Lean_Syntax_node1(v_a_2246_, v___y_2174_, v_type_1933_);
v___x_2295_ = l_Lean_Syntax_node2(v_a_2246_, v___y_2191_, v___x_2293_, v___x_2294_);
v___x_2296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_2297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2297_, 0, v_a_2246_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node3(v_a_2246_, v___x_2257_, v___x_2284_, v___x_2295_, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_node1(v_a_2246_, v___y_2174_, v___x_2298_);
lean_inc(v___x_2249_);
v___x_2300_ = l_Lean_Syntax_node4(v_a_2246_, v___x_2249_, v_fields_1926_, v___x_2251_, v___x_2255_, v___x_2299_);
v_ref_2301_ = l_Lean_replaceRef(v___x_2300_, v___y_2179_);
lean_inc(v_ref_2301_);
lean_inc(v___y_2185_);
lean_inc(v___y_2180_);
lean_inc(v___y_2166_);
v___x_2302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2302_, 0, v___y_2166_);
lean_ctor_set(v___x_2302_, 1, v___y_2170_);
lean_ctor_set(v___x_2302_, 2, v___y_2169_);
lean_ctor_set(v___x_2302_, 3, v___y_2180_);
lean_ctor_set(v___x_2302_, 4, v___y_2185_);
lean_ctor_set(v___x_2302_, 5, v_ref_2301_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1924_, v_ref_2301_, v___x_2302_, v_a_2247_);
lean_dec_ref(v___x_2302_);
lean_dec(v_ref_2301_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc_n(v_a_2304_, 29);
v_a_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2303_);
lean_inc(v___y_2178_);
lean_inc_n(v___y_2187_, 2);
v___x_2306_ = l_Lean_Syntax_node4(v___y_2187_, v___x_2229_, v___x_2230_, v___x_2238_, v___x_2242_, v___y_2178_);
v___x_2307_ = l_Lean_Syntax_node6(v___y_2187_, v___x_2204_, v___x_2207_, v___x_2208_, v___y_2178_, v___x_2210_, v___x_2227_, v___x_2306_);
lean_inc(v___y_2186_);
v___x_2308_ = l_Lean_Syntax_node2(v___y_2187_, v___y_2186_, v___x_2202_, v___x_2307_);
v___x_2309_ = lean_array_push(v___y_2168_, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2310_, 0, v_a_2304_);
lean_ctor_set(v___x_2310_, 1, v___x_2250_);
v___x_2311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_2169_, 6);
lean_inc_n(v___y_2170_, 6);
v___x_2313_ = l_Lean_addMacroScope(v___y_2170_, v___x_2312_, v___y_2169_);
lean_inc_n(v___y_2188_, 6);
v___x_2314_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2314_, 0, v_a_2304_);
lean_ctor_set(v___x_2314_, 1, v___x_2311_);
lean_ctor_set(v___x_2314_, 2, v___x_2313_);
lean_ctor_set(v___x_2314_, 3, v___y_2188_);
lean_inc_ref(v___y_2176_);
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2304_);
lean_ctor_set(v___x_2315_, 1, v___y_2176_);
lean_inc_ref(v___y_2175_);
lean_inc_n(v___y_2174_, 6);
v___x_2316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2316_, 0, v_a_2304_);
lean_ctor_set(v___x_2316_, 1, v___y_2174_);
lean_ctor_set(v___x_2316_, 2, v___y_2175_);
v___x_2317_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2319_ = l_Lean_addMacroScope(v___y_2170_, v___x_2318_, v___y_2169_);
v___x_2320_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2320_, 0, v_a_2304_);
lean_ctor_set(v___x_2320_, 1, v___x_2317_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
lean_ctor_set(v___x_2320_, 3, v___y_2188_);
lean_inc_ref_n(v___x_2316_, 13);
lean_inc_n(v___y_2162_, 2);
v___x_2321_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2162_, v___x_2320_, v___x_2316_);
lean_inc_ref(v___y_2193_);
v___x_2322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2304_);
lean_ctor_set(v___x_2322_, 1, v___y_2193_);
lean_inc_ref(v___x_2322_);
lean_inc(v___y_2197_);
v___x_2323_ = l_Lean_Syntax_node3(v_a_2304_, v___y_2197_, v___x_2322_, v___x_2316_, v___y_2167_);
v___x_2324_ = l_Lean_Syntax_node3(v_a_2304_, v___y_2174_, v___x_2316_, v___x_2316_, v___x_2323_);
lean_inc(v___x_2324_);
lean_inc_n(v___y_2192_, 2);
v___x_2325_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2192_, v___x_2321_, v___x_2324_);
v___x_2326_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2328_ = l_Lean_addMacroScope(v___y_2170_, v___x_2327_, v___y_2169_);
v___x_2329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2304_);
lean_ctor_set(v___x_2329_, 1, v___x_2326_);
lean_ctor_set(v___x_2329_, 2, v___x_2328_);
lean_ctor_set(v___x_2329_, 3, v___y_2188_);
v___x_2330_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2162_, v___x_2329_, v___x_2316_);
v___x_2331_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2192_, v___x_2330_, v___x_2324_);
v___x_2332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_2333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_2334_ = l_Lean_addMacroScope(v___y_2170_, v___x_2333_, v___y_2169_);
v___x_2335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2335_, 0, v_a_2304_);
lean_ctor_set(v___x_2335_, 1, v___x_2332_);
lean_ctor_set(v___x_2335_, 2, v___x_2334_);
lean_ctor_set(v___x_2335_, 3, v___y_2188_);
v___x_2336_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2162_, v___x_2335_, v___x_2316_);
v___x_2337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_2338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_2339_ = l_Lean_addMacroScope(v___y_2170_, v___x_2338_, v___y_2169_);
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_2196_, 2);
v___x_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___y_2196_);
v___x_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___y_2188_);
v___x_2343_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2343_, 0, v_a_2304_);
lean_ctor_set(v___x_2343_, 1, v___x_2337_);
lean_ctor_set(v___x_2343_, 2, v___x_2339_);
lean_ctor_set(v___x_2343_, 3, v___x_2342_);
v___x_2344_ = l_Lean_Syntax_node3(v_a_2304_, v___y_2197_, v___x_2322_, v___x_2316_, v___x_2343_);
v___x_2345_ = l_Lean_Syntax_node3(v_a_2304_, v___y_2174_, v___x_2316_, v___x_2316_, v___x_2344_);
v___x_2346_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2192_, v___x_2336_, v___x_2345_);
v___x_2347_ = l_Lean_Syntax_node6(v_a_2304_, v___y_2174_, v___x_2325_, v___x_2316_, v___x_2331_, v___x_2316_, v___x_2346_, v___x_2316_);
v___x_2348_ = l_Lean_Syntax_node1(v_a_2304_, v___y_2194_, v___x_2347_);
v___x_2349_ = l_Lean_Syntax_node1(v_a_2304_, v___y_2184_, v___x_2316_);
lean_inc_ref(v___y_2181_);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2304_);
lean_ctor_set(v___x_2350_, 1, v___y_2181_);
v___x_2351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2354_ = l_Lean_addMacroScope(v___y_2170_, v___x_2353_, v___y_2169_);
lean_inc_ref(v___y_2182_);
v___x_2355_ = l_Lean_Name_mkStr2(v___y_2182_, v___x_2351_);
lean_inc(v___x_2355_);
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v___y_2196_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
v___x_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___y_2188_);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2356_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2360_, 0, v_a_2304_);
lean_ctor_set(v___x_2360_, 1, v___x_2352_);
lean_ctor_set(v___x_2360_, 2, v___x_2354_);
lean_ctor_set(v___x_2360_, 3, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node2(v_a_2304_, v___y_2174_, v___x_2350_, v___x_2360_);
lean_inc_ref(v___y_2165_);
v___x_2362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_a_2304_);
lean_ctor_set(v___x_2362_, 1, v___y_2165_);
v___x_2363_ = l_Lean_Syntax_node6(v_a_2304_, v___y_2195_, v___x_2315_, v___x_2316_, v___x_2348_, v___x_2349_, v___x_2361_, v___x_2362_);
v___x_2364_ = l_Lean_Syntax_node1(v_a_2304_, v___y_2174_, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_node4(v_a_2304_, v___x_2249_, v___x_2300_, v___x_2310_, v___x_2314_, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2309_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v_a_1915_ = v___x_2366_;
v_a_1916_ = v_a_2305_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v___x_2300_);
lean_dec(v___x_2249_);
lean_dec(v___x_2242_);
lean_dec(v___x_2238_);
lean_dec_ref(v___x_2230_);
lean_dec(v___x_2229_);
lean_dec(v___x_2227_);
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2208_);
lean_dec(v___x_2207_);
lean_dec(v___x_2204_);
lean_dec(v___x_2202_);
lean_dec(v___y_2197_);
lean_dec(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec(v___y_2187_);
lean_dec(v___y_2184_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2162_);
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v_a_2367_ = lean_ctor_get(v___x_2303_, 0);
v_a_2368_ = lean_ctor_get(v___x_2303_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2303_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_inc(v_a_2367_);
lean_dec(v___x_2303_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2367_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v___x_2242_);
lean_dec(v___x_2238_);
lean_dec_ref(v___x_2230_);
lean_dec(v___x_2229_);
lean_dec(v___x_2227_);
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2208_);
lean_dec(v___x_2207_);
lean_dec(v___x_2204_);
lean_dec(v___x_2202_);
lean_dec(v___y_2197_);
lean_dec(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec(v___y_2187_);
lean_dec(v___y_2184_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2162_);
lean_dec(v_fields_1926_);
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v_a_2376_ = lean_ctor_get(v___x_2245_, 0);
v_a_2377_ = lean_ctor_get(v___x_2245_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2245_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_inc(v_a_2376_);
lean_dec(v___x_2245_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2376_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
v___jp_2385_:
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1924_, v___y_2401_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v_a_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_n(v_a_2421_, 2);
v_a_2422_ = lean_ctor_get(v___x_2420_, 1);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2420_);
v___x_2423_ = l_Lean_mkIdentFrom(v_id_1931_, v___y_2419_, v___x_1924_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2398_);
v___x_2424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2421_);
lean_ctor_set(v___x_2424_, 1, v___y_2398_);
lean_ctor_set(v___x_2424_, 2, v___y_2397_);
if (lean_obj_tag(v_vis_x3f_1906_) == 1)
{
lean_object* v_val_2425_; lean_object* v___x_2426_; 
v_val_2425_ = lean_ctor_get(v_vis_x3f_1906_, 0);
lean_inc(v_val_2425_);
v___x_2426_ = l_Array_mkArray1___redArg(v_val_2425_);
v___y_2162_ = v___y_2386_;
v___y_2163_ = v_a_2422_;
v___y_2164_ = v___y_2387_;
v___y_2165_ = v___y_2389_;
v___y_2166_ = v___y_2388_;
v___y_2167_ = v___y_2390_;
v___y_2168_ = v___y_2392_;
v___y_2169_ = v___y_2391_;
v___y_2170_ = v___y_2395_;
v___y_2171_ = v___y_2394_;
v___y_2172_ = v___y_2393_;
v___y_2173_ = v___y_2396_;
v___y_2174_ = v___y_2398_;
v___y_2175_ = v___y_2397_;
v___y_2176_ = v___y_2399_;
v___y_2177_ = v___y_2400_;
v___y_2178_ = v___x_2424_;
v___y_2179_ = v___y_2401_;
v___y_2180_ = v___y_2402_;
v___y_2181_ = v___y_2403_;
v___y_2182_ = v___y_2404_;
v___y_2183_ = v___y_2405_;
v___y_2184_ = v___y_2406_;
v___y_2185_ = v___y_2407_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v_a_2421_;
v___y_2188_ = v___y_2409_;
v___y_2189_ = v___x_2423_;
v___y_2190_ = v___y_2411_;
v___y_2191_ = v___y_2410_;
v___y_2192_ = v___y_2412_;
v___y_2193_ = v___y_2413_;
v___y_2194_ = v___y_2414_;
v___y_2195_ = v___y_2415_;
v___y_2196_ = v___y_2416_;
v___y_2197_ = v___y_2418_;
v___y_2198_ = v___y_2417_;
v___y_2199_ = v___x_2426_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2162_ = v___y_2386_;
v___y_2163_ = v_a_2422_;
v___y_2164_ = v___y_2387_;
v___y_2165_ = v___y_2389_;
v___y_2166_ = v___y_2388_;
v___y_2167_ = v___y_2390_;
v___y_2168_ = v___y_2392_;
v___y_2169_ = v___y_2391_;
v___y_2170_ = v___y_2395_;
v___y_2171_ = v___y_2394_;
v___y_2172_ = v___y_2393_;
v___y_2173_ = v___y_2396_;
v___y_2174_ = v___y_2398_;
v___y_2175_ = v___y_2397_;
v___y_2176_ = v___y_2399_;
v___y_2177_ = v___y_2400_;
v___y_2178_ = v___x_2424_;
v___y_2179_ = v___y_2401_;
v___y_2180_ = v___y_2402_;
v___y_2181_ = v___y_2403_;
v___y_2182_ = v___y_2404_;
v___y_2183_ = v___y_2405_;
v___y_2184_ = v___y_2406_;
v___y_2185_ = v___y_2407_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v_a_2421_;
v___y_2188_ = v___y_2409_;
v___y_2189_ = v___x_2423_;
v___y_2190_ = v___y_2411_;
v___y_2191_ = v___y_2410_;
v___y_2192_ = v___y_2412_;
v___y_2193_ = v___y_2413_;
v___y_2194_ = v___y_2414_;
v___y_2195_ = v___y_2415_;
v___y_2196_ = v___y_2416_;
v___y_2197_ = v___y_2418_;
v___y_2198_ = v___y_2417_;
v___y_2199_ = v___x_2427_;
goto v___jp_2161_;
}
}
else
{
lean_object* v_a_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v___y_2412_);
lean_dec(v___y_2410_);
lean_dec(v___y_2406_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2390_);
lean_dec(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec(v_fields_1926_);
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v_a_2428_ = lean_ctor_get(v___x_2420_, 0);
v_a_2429_ = lean_ctor_get(v___x_2420_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2420_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_inc(v_a_2428_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2428_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_inc_ref_n(v___y_2449_, 2);
v___x_2456_ = l_Array_append___redArg(v___y_2449_, v___y_2455_);
lean_dec_ref(v___y_2455_);
lean_inc_n(v___y_2450_, 19);
lean_inc_n(v___y_2442_, 69);
v___x_2457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2457_, 0, v___y_2442_);
lean_ctor_set(v___x_2457_, 1, v___y_2450_);
lean_ctor_set(v___x_2457_, 2, v___x_2456_);
lean_inc_n(v___y_2451_, 35);
lean_inc(v___y_2446_);
v___x_2458_ = l_Lean_Syntax_node7(v___y_2442_, v___y_2446_, v___y_2451_, v___y_2451_, v___x_2457_, v___y_2451_, v___y_2451_, v___y_2451_, v___y_2451_);
v___x_2459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_2447_, 4);
lean_inc_ref_n(v___y_2445_, 15);
lean_inc_ref_n(v___y_2439_, 15);
v___x_2460_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___y_2447_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2442_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_2464_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___y_2447_, v___x_2463_);
lean_inc(v___y_2454_);
lean_inc(v___x_2464_);
v___x_2465_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2464_, v___y_2454_, v___y_2451_);
v___x_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_2467_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___y_2447_, v___x_2466_);
v___x_2468_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_2469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_2470_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___y_2442_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_2474_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2473_);
v___x_2475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_2476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_2443_, 8);
lean_inc_n(v___y_2448_, 8);
v___x_2477_ = l_Lean_addMacroScope(v___y_2448_, v___x_2476_, v___y_2443_);
v___x_2478_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_2479_ = lean_box(0);
v___x_2480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_2481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2481_, 0, v___y_2442_);
lean_ctor_set(v___x_2481_, 1, v___x_2475_);
lean_ctor_set(v___x_2481_, 2, v___x_2477_);
lean_ctor_set(v___x_2481_, 3, v___x_2480_);
lean_inc(v_type_1933_);
lean_inc(v_structTy_1904_);
v___x_2482_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2450_, v_structTy_1904_, v_type_1933_);
lean_inc_n(v___x_2474_, 2);
v___x_2483_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2474_, v___x_2481_, v___x_2482_);
lean_inc(v___x_2470_);
v___x_2484_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2470_, v___x_2472_, v___x_2483_);
v___x_2485_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_2484_);
v___x_2486_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2467_, v___y_2451_, v___x_2485_);
v___x_2487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_2488_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___y_2447_, v___x_2487_);
v___x_2489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___y_2442_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_2492_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2491_);
v___x_2493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_2494_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2493_);
v___x_2495_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_2496_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2495_);
v___x_2497_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_2498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_2499_ = l_Lean_addMacroScope(v___y_2448_, v___x_2498_, v___y_2443_);
v___x_2500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_2501_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2501_, 0, v___y_2442_);
lean_ctor_set(v___x_2501_, 1, v___x_2497_);
lean_ctor_set(v___x_2501_, 2, v___x_2499_);
lean_ctor_set(v___x_2501_, 3, v___x_2500_);
lean_inc_n(v___x_2496_, 5);
v___x_2502_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2496_, v___x_2501_, v___y_2451_);
v___x_2503_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_2505_ = l_Lean_addMacroScope(v___y_2448_, v___x_2504_, v___y_2443_);
v___x_2506_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2442_);
lean_ctor_set(v___x_2506_, 1, v___x_2503_);
lean_ctor_set(v___x_2506_, 2, v___x_2505_);
lean_ctor_set(v___x_2506_, 3, v___x_2479_);
lean_inc_ref_n(v___x_2506_, 3);
v___x_2507_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_2509_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2508_);
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_2511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___y_2442_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_2513_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2512_);
v___x_2514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_2515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___y_2442_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_inc_n(v_id_1931_, 3);
v___x_2516_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2513_, v___x_2506_, v___x_2515_, v_id_1931_);
lean_inc(v___x_2516_);
lean_inc_ref_n(v___x_2511_, 5);
lean_inc_n(v___x_2509_, 6);
v___x_2517_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2516_);
lean_inc(v___x_2507_);
v___x_2518_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___x_2507_, v___y_2451_, v___x_2517_);
lean_inc_n(v___x_2494_, 6);
v___x_2519_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2502_, v___x_2518_);
v___x_2520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_2521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_2522_ = l_Lean_addMacroScope(v___y_2448_, v___x_2521_, v___y_2443_);
v___x_2523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_2524_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2524_, 0, v___y_2442_);
lean_ctor_set(v___x_2524_, 1, v___x_2520_);
lean_ctor_set(v___x_2524_, 2, v___x_2522_);
lean_ctor_set(v___x_2524_, 3, v___x_2523_);
v___x_2525_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2496_, v___x_2524_, v___y_2451_);
v___x_2526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_2527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_2528_ = l_Lean_addMacroScope(v___y_2448_, v___x_2527_, v___y_2443_);
v___x_2529_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2529_, 0, v___y_2442_);
lean_ctor_set(v___x_2529_, 1, v___x_2526_);
lean_ctor_set(v___x_2529_, 2, v___x_2528_);
lean_ctor_set(v___x_2529_, 3, v___x_2479_);
lean_inc_ref(v___x_2529_);
v___x_2530_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2450_, v___x_2529_, v___x_2506_);
v___x_2531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_2532_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2442_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2442_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2450_, v___x_2507_, v___x_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = l_Lean_SourceInfo_fromRef(v___x_2538_, v___x_1924_);
lean_inc(v___x_2539_);
v___x_2540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v___y_2450_);
lean_ctor_set(v___x_2540_, 2, v___y_2449_);
v___x_2541_ = l_Lean_Syntax_node2(v___x_2539_, v___x_2496_, v_id_1931_, v___x_2540_);
v___x_2542_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2529_);
v___x_2543_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___y_2451_, v___y_2451_, v___x_2542_);
lean_inc(v___x_2541_);
v___x_2544_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2541_, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_2544_);
lean_inc_n(v___x_2492_, 3);
v___x_2546_ = l_Lean_Syntax_node1(v___y_2442_, v___x_2492_, v___x_2545_);
v___x_2547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_2548_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2547_);
lean_inc(v___x_2548_);
v___x_2549_ = l_Lean_Syntax_node1(v___y_2442_, v___x_2548_, v___y_2451_);
v___x_2550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_2551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2442_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
lean_inc_ref(v___x_2551_);
lean_inc(v___x_2549_);
lean_inc(v___x_2537_);
lean_inc_ref(v___x_2534_);
lean_inc_n(v___x_2532_, 2);
v___x_2552_ = l_Lean_Syntax_node6(v___y_2442_, v___x_2532_, v___x_2534_, v___x_2537_, v___x_2546_, v___x_2549_, v___y_2451_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___x_2530_, v___y_2451_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2525_, v___x_2554_);
v___x_2556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_2557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_2558_ = l_Lean_addMacroScope(v___y_2448_, v___x_2557_, v___y_2443_);
v___x_2559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_2560_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2560_, 0, v___y_2442_);
lean_ctor_set(v___x_2560_, 1, v___x_2556_);
lean_ctor_set(v___x_2560_, 2, v___x_2558_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2496_, v___x_2560_, v___y_2451_);
v___x_2562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_2563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_2564_ = l_Lean_addMacroScope(v___y_2448_, v___x_2563_, v___y_2443_);
v___x_2565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2442_);
lean_ctor_set(v___x_2565_, 1, v___x_2562_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
lean_ctor_set(v___x_2565_, 3, v___x_2479_);
lean_inc_ref(v___x_2565_);
v___x_2566_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2450_, v___x_2565_, v___x_2506_);
v___x_2567_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_2516_);
v___x_2568_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2474_, v___x_2565_, v___x_2567_);
v___x_2569_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2568_);
v___x_2570_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___y_2451_, v___y_2451_, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2541_, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_2571_);
v___x_2573_ = l_Lean_Syntax_node1(v___y_2442_, v___x_2492_, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node6(v___y_2442_, v___x_2532_, v___x_2534_, v___x_2537_, v___x_2573_, v___x_2549_, v___y_2451_, v___x_2551_);
v___x_2575_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2574_);
v___x_2576_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___x_2566_, v___y_2451_, v___x_2575_);
v___x_2577_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2561_, v___x_2576_);
v___x_2578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_2579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_2580_ = l_Lean_addMacroScope(v___y_2448_, v___x_2579_, v___y_2443_);
v___x_2581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2581_, 0, v___y_2442_);
lean_ctor_set(v___x_2581_, 1, v___x_2578_);
lean_ctor_set(v___x_2581_, 2, v___x_2580_);
lean_ctor_set(v___x_2581_, 3, v___x_2479_);
v___x_2582_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2496_, v___x_2581_, v___y_2451_);
v___x_2583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_2584_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2583_);
v___x_2585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___y_2442_);
lean_ctor_set(v___x_2585_, 1, v___x_2583_);
v___x_2586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_2587_ = l_Lean_Name_mkStr4(v___y_2439_, v___y_2445_, v___x_2468_, v___x_2586_);
lean_inc(v___x_1905_);
v___x_2588_ = l_Lean_Syntax_node1(v___y_2442_, v___y_2450_, v___x_1905_);
v___x_2589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_2590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___y_2442_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
lean_inc(v_defVal_1934_);
v___x_2591_ = l_Lean_Syntax_node4(v___y_2442_, v___x_2587_, v___x_2588_, v___y_2451_, v___x_2590_, v_defVal_1934_);
v___x_2592_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2584_, v___x_2585_, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2509_, v___x_2511_, v___y_2451_, v___x_2592_);
v___x_2594_ = l_Lean_Syntax_node3(v___y_2442_, v___y_2450_, v___y_2451_, v___y_2451_, v___x_2593_);
v___x_2595_ = l_Lean_Syntax_node2(v___y_2442_, v___x_2494_, v___x_2582_, v___x_2594_);
v___x_2596_ = l_Lean_Syntax_node7(v___y_2442_, v___y_2450_, v___x_2519_, v___y_2451_, v___x_2555_, v___y_2451_, v___x_2577_, v___y_2451_, v___x_2595_);
v___x_2597_ = l_Lean_Syntax_node1(v___y_2442_, v___x_2492_, v___x_2596_);
v___x_2598_ = l_Lean_Syntax_node3(v___y_2442_, v___x_2488_, v___x_2490_, v___x_2597_, v___y_2451_);
v___x_2599_ = l_Lean_Syntax_node5(v___y_2442_, v___x_2460_, v___x_2462_, v___x_2465_, v___x_2486_, v___x_2598_, v___y_2451_);
lean_inc(v___y_2444_);
v___x_2600_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2444_, v___x_2458_, v___x_2599_);
v___x_2601_ = lean_array_push(v_cmds_1925_, v___x_2600_);
lean_inc(v___x_2437_);
v___x_2602_ = l_Lake_Name_quoteFrom(v_id_1931_, v___x_2437_, v___x_1924_);
if (v_parent_1935_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
lean_dec(v___x_2437_);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_array_get_size(v_ids_1932_);
v___x_2605_ = lean_nat_dec_lt(v___x_2603_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
lean_dec(v___x_2602_);
lean_dec(v___x_2548_);
lean_dec(v___x_2532_);
lean_dec(v___x_2509_);
lean_dec(v___x_2496_);
lean_dec(v___x_2494_);
lean_dec(v___x_2492_);
lean_dec(v___x_2474_);
lean_dec(v___x_2470_);
lean_dec(v___x_2464_);
lean_dec(v___y_2454_);
lean_del_object(v___x_1928_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2601_);
lean_ctor_set(v___x_2606_, 1, v_fields_1926_);
v_a_1915_ = v___x_2606_;
v_a_1916_ = v___y_1913_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2607_ = lean_array_fget_borrowed(v_ids_1932_, v___x_2603_);
v___x_2608_ = l_Lean_TSyntax_getId(v___x_2607_);
lean_inc(v___x_2608_);
lean_inc(v___x_2607_);
v___x_2609_ = l_Lake_Name_quoteFrom(v___x_2607_, v___x_2608_, v___x_1924_);
v___x_2610_ = l_Lean_Name_hasMacroScopes(v___x_2608_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1907_, v___x_2608_);
lean_inc(v___x_2607_);
v___y_2106_ = v___x_2496_;
v___y_2107_ = v___x_2470_;
v___y_2108_ = v___y_2441_;
v___y_2109_ = v___x_2550_;
v___y_2110_ = v___x_2602_;
v___y_2111_ = v___y_2443_;
v___y_2112_ = v___x_2601_;
v___y_2113_ = v___y_2447_;
v___y_2114_ = v___y_2448_;
v___y_2115_ = v___x_2607_;
v___y_2116_ = v___y_2446_;
v___y_2117_ = v___x_2468_;
v___y_2118_ = v___y_2449_;
v___y_2119_ = v___y_2450_;
v___y_2120_ = v___x_2533_;
v___y_2121_ = v___x_2464_;
v___y_2122_ = v___y_2452_;
v___y_2123_ = v___y_2453_;
v___y_2124_ = v___x_2471_;
v___y_2125_ = v___x_2609_;
v___y_2126_ = v___x_2478_;
v___y_2127_ = v___x_2604_;
v___y_2128_ = v___y_2439_;
v___y_2129_ = v___x_2548_;
v___y_2130_ = v___y_2440_;
v___y_2131_ = v___y_2444_;
v___y_2132_ = v___x_2603_;
v___y_2133_ = v___x_2479_;
v___y_2134_ = v___x_2474_;
v___y_2135_ = v___y_2445_;
v___y_2136_ = v___x_2494_;
v___y_2137_ = v___x_2510_;
v___y_2138_ = v___x_2492_;
v___y_2139_ = v___x_2532_;
v___y_2140_ = v___x_2479_;
v___y_2141_ = v___y_2454_;
v___y_2142_ = v___x_2509_;
v___y_2143_ = v___x_2611_;
goto v___jp_2105_;
}
else
{
lean_object* v_view_2612_; lean_object* v_name_2613_; lean_object* v_imported_2614_; lean_object* v_ctx_2615_; lean_object* v_scopes_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2625_; 
v_view_2612_ = l_Lean_extractMacroScopes(v___x_2608_);
v_name_2613_ = lean_ctor_get(v_view_2612_, 0);
v_imported_2614_ = lean_ctor_get(v_view_2612_, 1);
v_ctx_2615_ = lean_ctor_get(v_view_2612_, 2);
v_scopes_2616_ = lean_ctor_get(v_view_2612_, 3);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_view_2612_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2618_ = v_view_2612_;
v_isShared_2619_ = v_isSharedCheck_2625_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_scopes_2616_);
lean_inc(v_ctx_2615_);
lean_inc(v_imported_2614_);
lean_inc(v_name_2613_);
lean_dec(v_view_2612_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2625_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1907_, v_name_2613_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_imported_2614_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_ctx_2615_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_scopes_2616_);
v___x_2622_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_MacroScopesView_review(v___x_2622_);
lean_inc(v___x_2607_);
v___y_2106_ = v___x_2496_;
v___y_2107_ = v___x_2470_;
v___y_2108_ = v___y_2441_;
v___y_2109_ = v___x_2550_;
v___y_2110_ = v___x_2602_;
v___y_2111_ = v___y_2443_;
v___y_2112_ = v___x_2601_;
v___y_2113_ = v___y_2447_;
v___y_2114_ = v___y_2448_;
v___y_2115_ = v___x_2607_;
v___y_2116_ = v___y_2446_;
v___y_2117_ = v___x_2468_;
v___y_2118_ = v___y_2449_;
v___y_2119_ = v___y_2450_;
v___y_2120_ = v___x_2533_;
v___y_2121_ = v___x_2464_;
v___y_2122_ = v___y_2452_;
v___y_2123_ = v___y_2453_;
v___y_2124_ = v___x_2471_;
v___y_2125_ = v___x_2609_;
v___y_2126_ = v___x_2478_;
v___y_2127_ = v___x_2604_;
v___y_2128_ = v___y_2439_;
v___y_2129_ = v___x_2548_;
v___y_2130_ = v___y_2440_;
v___y_2131_ = v___y_2444_;
v___y_2132_ = v___x_2603_;
v___y_2133_ = v___x_2479_;
v___y_2134_ = v___x_2474_;
v___y_2135_ = v___y_2445_;
v___y_2136_ = v___x_2494_;
v___y_2137_ = v___x_2510_;
v___y_2138_ = v___x_2492_;
v___y_2139_ = v___x_2532_;
v___y_2140_ = v___x_2479_;
v___y_2141_ = v___y_2454_;
v___y_2142_ = v___x_2509_;
v___y_2143_ = v___x_2623_;
goto v___jp_2105_;
}
}
}
}
}
else
{
uint8_t v___x_2626_; 
lean_del_object(v___x_1928_);
v___x_2626_ = l_Lean_Name_hasMacroScopes(v___x_2437_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1907_, v___x_2437_);
v___y_2386_ = v___x_2496_;
v___y_2387_ = v___x_2470_;
v___y_2388_ = v___y_2441_;
v___y_2389_ = v___x_2550_;
v___y_2390_ = v___x_2602_;
v___y_2391_ = v___y_2443_;
v___y_2392_ = v___x_2601_;
v___y_2393_ = v___y_2446_;
v___y_2394_ = v___y_2447_;
v___y_2395_ = v___y_2448_;
v___y_2396_ = v___x_2468_;
v___y_2397_ = v___y_2449_;
v___y_2398_ = v___y_2450_;
v___y_2399_ = v___x_2533_;
v___y_2400_ = v___x_2464_;
v___y_2401_ = v___y_2452_;
v___y_2402_ = v___y_2453_;
v___y_2403_ = v___x_2471_;
v___y_2404_ = v___x_2478_;
v___y_2405_ = v___y_2439_;
v___y_2406_ = v___x_2548_;
v___y_2407_ = v___y_2440_;
v___y_2408_ = v___y_2444_;
v___y_2409_ = v___x_2479_;
v___y_2410_ = v___x_2474_;
v___y_2411_ = v___y_2445_;
v___y_2412_ = v___x_2494_;
v___y_2413_ = v___x_2510_;
v___y_2414_ = v___x_2492_;
v___y_2415_ = v___x_2532_;
v___y_2416_ = v___x_2479_;
v___y_2417_ = v___y_2454_;
v___y_2418_ = v___x_2509_;
v___y_2419_ = v___x_2627_;
goto v___jp_2385_;
}
else
{
lean_object* v_view_2628_; lean_object* v_name_2629_; lean_object* v_imported_2630_; lean_object* v_ctx_2631_; lean_object* v_scopes_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2641_; 
v_view_2628_ = l_Lean_extractMacroScopes(v___x_2437_);
v_name_2629_ = lean_ctor_get(v_view_2628_, 0);
v_imported_2630_ = lean_ctor_get(v_view_2628_, 1);
v_ctx_2631_ = lean_ctor_get(v_view_2628_, 2);
v_scopes_2632_ = lean_ctor_get(v_view_2628_, 3);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_view_2628_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2634_ = v_view_2628_;
v_isShared_2635_ = v_isSharedCheck_2641_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_scopes_2632_);
lean_inc(v_ctx_2631_);
lean_inc(v_imported_2630_);
lean_inc(v_name_2629_);
lean_dec(v_view_2628_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2641_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1907_, v_name_2629_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_imported_2630_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_ctx_2631_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_scopes_2632_);
v___x_2638_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_MacroScopesView_review(v___x_2638_);
v___y_2386_ = v___x_2496_;
v___y_2387_ = v___x_2470_;
v___y_2388_ = v___y_2441_;
v___y_2389_ = v___x_2550_;
v___y_2390_ = v___x_2602_;
v___y_2391_ = v___y_2443_;
v___y_2392_ = v___x_2601_;
v___y_2393_ = v___y_2446_;
v___y_2394_ = v___y_2447_;
v___y_2395_ = v___y_2448_;
v___y_2396_ = v___x_2468_;
v___y_2397_ = v___y_2449_;
v___y_2398_ = v___y_2450_;
v___y_2399_ = v___x_2533_;
v___y_2400_ = v___x_2464_;
v___y_2401_ = v___y_2452_;
v___y_2402_ = v___y_2453_;
v___y_2403_ = v___x_2471_;
v___y_2404_ = v___x_2478_;
v___y_2405_ = v___y_2439_;
v___y_2406_ = v___x_2548_;
v___y_2407_ = v___y_2440_;
v___y_2408_ = v___y_2444_;
v___y_2409_ = v___x_2479_;
v___y_2410_ = v___x_2474_;
v___y_2411_ = v___y_2445_;
v___y_2412_ = v___x_2494_;
v___y_2413_ = v___x_2510_;
v___y_2414_ = v___x_2492_;
v___y_2415_ = v___x_2532_;
v___y_2416_ = v___x_2479_;
v___y_2417_ = v___y_2454_;
v___y_2418_ = v___x_2509_;
v___y_2419_ = v___x_2639_;
goto v___jp_2385_;
}
}
}
}
}
v___jp_2642_:
{
lean_object* v_methods_2644_; lean_object* v_quotContext_2645_; lean_object* v_currMacroScope_2646_; lean_object* v_currRecDepth_2647_; lean_object* v_maxRecDepth_2648_; lean_object* v_ref_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_methods_2644_ = lean_ctor_get(v___y_1912_, 0);
v_quotContext_2645_ = lean_ctor_get(v___y_1912_, 1);
v_currMacroScope_2646_ = lean_ctor_get(v___y_1912_, 2);
v_currRecDepth_2647_ = lean_ctor_get(v___y_1912_, 3);
v_maxRecDepth_2648_ = lean_ctor_get(v___y_1912_, 4);
v_ref_2649_ = lean_ctor_get(v___y_1912_, 5);
v___x_2650_ = l_Lean_mkIdentFrom(v_id_1931_, v___y_2643_, v___x_1924_);
v___x_2651_ = l_Lean_SourceInfo_fromRef(v_ref_2649_, v___x_1924_);
v___x_2652_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2653_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2654_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_2655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_2656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_2657_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2658_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_2651_);
v___x_2659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2651_);
lean_ctor_set(v___x_2659_, 1, v___x_2657_);
lean_ctor_set(v___x_2659_, 2, v___x_2658_);
if (lean_obj_tag(v_vis_x3f_1906_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
v_val_2660_ = lean_ctor_get(v_vis_x3f_1906_, 0);
lean_inc(v_val_2660_);
v___x_2661_ = l_Array_mkArray1___redArg(v_val_2660_);
v___y_2439_ = v___x_2652_;
v___y_2440_ = v_maxRecDepth_2648_;
v___y_2441_ = v_methods_2644_;
v___y_2442_ = v___x_2651_;
v___y_2443_ = v_currMacroScope_2646_;
v___y_2444_ = v___x_2655_;
v___y_2445_ = v___x_2653_;
v___y_2446_ = v___x_2656_;
v___y_2447_ = v___x_2654_;
v___y_2448_ = v_quotContext_2645_;
v___y_2449_ = v___x_2658_;
v___y_2450_ = v___x_2657_;
v___y_2451_ = v___x_2659_;
v___y_2452_ = v_ref_2649_;
v___y_2453_ = v_currRecDepth_2647_;
v___y_2454_ = v___x_2650_;
v___y_2455_ = v___x_2661_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2439_ = v___x_2652_;
v___y_2440_ = v_maxRecDepth_2648_;
v___y_2441_ = v_methods_2644_;
v___y_2442_ = v___x_2651_;
v___y_2443_ = v_currMacroScope_2646_;
v___y_2444_ = v___x_2655_;
v___y_2445_ = v___x_2653_;
v___y_2446_ = v___x_2656_;
v___y_2447_ = v___x_2654_;
v___y_2448_ = v_quotContext_2645_;
v___y_2449_ = v___x_2658_;
v___y_2450_ = v___x_2657_;
v___y_2451_ = v___x_2659_;
v___y_2452_ = v_ref_2649_;
v___y_2453_ = v_currRecDepth_2647_;
v___y_2454_ = v___x_2650_;
v___y_2455_ = v___x_2662_;
goto v___jp_2438_;
}
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_b_1911_);
lean_ctor_set(v___x_2680_, 1, v___y_1913_);
return v___x_2680_;
}
v___jp_1914_:
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1909_, v___x_1917_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1904_, v___x_1905_, v_vis_x3f_1906_, v_structId_1907_, v_as_1908_, v___x_1918_, v_stop_1910_, v_a_1915_, v___y_1912_, v_a_1916_);
return v___x_1919_;
}
v___jp_1920_:
{
if (lean_obj_tag(v___y_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_a_1923_; 
v_a_1922_ = lean_ctor_get(v___y_1921_, 0);
lean_inc(v_a_1922_);
v_a_1923_ = lean_ctor_get(v___y_1921_, 1);
lean_inc(v_a_1923_);
lean_dec_ref(v___y_1921_);
v_a_1915_ = v_a_1922_;
v_a_1916_ = v_a_1923_;
goto v___jp_1914_;
}
else
{
lean_dec(v_vis_x3f_1906_);
lean_dec(v___x_1905_);
lean_dec(v_structTy_1904_);
return v___y_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___boxed(lean_object* v_structTy_2681_, lean_object* v___x_2682_, lean_object* v_vis_x3f_2683_, lean_object* v_structId_2684_, lean_object* v_as_2685_, lean_object* v_i_2686_, lean_object* v_stop_2687_, lean_object* v_b_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
size_t v_i_boxed_2691_; size_t v_stop_boxed_2692_; lean_object* v_res_2693_; 
v_i_boxed_2691_ = lean_unbox_usize(v_i_2686_);
lean_dec(v_i_2686_);
v_stop_boxed_2692_ = lean_unbox_usize(v_stop_2687_);
lean_dec(v_stop_2687_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2681_, v___x_2682_, v_vis_x3f_2683_, v_structId_2684_, v_as_2685_, v_i_boxed_2691_, v_stop_boxed_2692_, v_b_2688_, v___y_2689_, v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec_ref(v_as_2685_);
lean_dec(v_structId_2684_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(size_t v_sz_2694_, size_t v_i_2695_, lean_object* v_bs_2696_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_usize_dec_lt(v_i_2695_, v_sz_2694_);
if (v___x_2697_ == 0)
{
return v_bs_2696_;
}
else
{
lean_object* v_v_2698_; lean_object* v_id_2699_; lean_object* v___x_2700_; lean_object* v_bs_x27_2701_; size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
v_v_2698_ = lean_array_uget_borrowed(v_bs_2696_, v_i_2695_);
v_id_2699_ = lean_ctor_get(v_v_2698_, 2);
lean_inc(v_id_2699_);
v___x_2700_ = lean_unsigned_to_nat(0u);
v_bs_x27_2701_ = lean_array_uset(v_bs_2696_, v_i_2695_, v___x_2700_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_add(v_i_2695_, v___x_2702_);
v___x_2704_ = lean_array_uset(v_bs_x27_2701_, v_i_2695_, v_id_2699_);
v_i_2695_ = v___x_2703_;
v_bs_2696_ = v___x_2704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0___boxed(lean_object* v_sz_2706_, lean_object* v_i_2707_, lean_object* v_bs_2708_){
_start:
{
size_t v_sz_boxed_2709_; size_t v_i_boxed_2710_; lean_object* v_res_2711_; 
v_sz_boxed_2709_ = lean_unbox_usize(v_sz_2706_);
lean_dec(v_sz_2706_);
v_i_boxed_2710_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_boxed_2709_, v_i_boxed_2710_, v_bs_2708_);
return v_res_2711_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = l_Lean_firstFrontendMacroScope;
v___x_2721_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4));
v___x_2722_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1));
v___x_2723_ = l_Lean_addMacroScope(v___x_2722_, v___x_2721_, v___x_2720_);
return v___x_2723_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7));
v___x_2728_ = l_String_toRawSubstring_x27(v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2735_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10));
v___x_2736_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5);
v___x_2737_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8);
v___x_2738_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_2739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v___x_2737_);
lean_ctor_set(v___x_2739_, 2, v___x_2736_);
lean_ctor_set(v___x_2739_, 3, v___x_2735_);
return v___x_2739_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_data_2742_; 
v___x_2740_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11);
v___x_2741_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v_data_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_data_2742_, 0, v___x_2741_);
lean_ctor_set(v_data_2742_, 1, v___x_2740_);
return v_data_2742_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2754_ = l_Lean_mkAtom(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18));
v___x_2763_ = l_String_toRawSubstring_x27(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_2785_ = l_String_toRawSubstring_x27(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2795_ = l_String_toRawSubstring_x27(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37));
v___x_2805_ = l_String_toRawSubstring_x27(v___x_2804_);
return v___x_2805_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40));
v___x_2810_ = l_Lean_mkAtom(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2811_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2812_ = lean_unsigned_to_nat(3u);
v___x_2813_ = lean_mk_empty_array_with_capacity(v___x_2812_);
v___x_2814_ = lean_array_push(v___x_2813_, v___x_2811_);
return v___x_2814_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2816_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42);
v___x_2817_ = lean_array_push(v___x_2816_, v___x_2815_);
return v___x_2817_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2834_ = l_String_toRawSubstring_x27(v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(lean_object* v_vis_x3f_2861_, lean_object* v_structId_2862_, lean_object* v_structArity_2863_, lean_object* v_structTy_2864_, lean_object* v_views_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_quotContext_2868_; lean_object* v_currMacroScope_2869_; lean_object* v_ref_2870_; lean_object* v___x_2871_; lean_object* v_a_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3363_; 
v_quotContext_2868_ = lean_ctor_get(v_a_2866_, 1);
v_currMacroScope_2869_ = lean_ctor_get(v_a_2866_, 2);
v_ref_2870_ = lean_ctor_get(v_a_2866_, 5);
v___x_2871_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v_a_2867_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_a_2873_ = lean_ctor_get(v___x_2871_, 1);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_2875_ = v___x_2871_;
v_isShared_2876_ = v_isSharedCheck_3363_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3363_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v_data_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; size_t v_sz_2890_; size_t v___x_2891_; lean_object* v___x_2892_; size_t v_sz_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v_a_3322_; lean_object* v_a_3323_; lean_object* v___y_3342_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = 0;
v___x_2879_ = lean_box(0);
v_data_2880_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12);
v___x_2881_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2882_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2883_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13));
v___x_2884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
lean_inc_n(v_a_2872_, 9);
v___x_2885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2885_, 0, v_a_2872_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2887_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_2888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2888_, 0, v_a_2872_);
lean_ctor_set(v___x_2888_, 1, v___x_2886_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
v___x_2889_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14));
v_sz_2890_ = lean_array_size(v_views_2865_);
v___x_2891_ = ((size_t)0ULL);
lean_inc_ref(v_views_2865_);
v___x_2892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_2890_, v___x_2891_, v_views_2865_);
v_sz_2893_ = lean_array_size(v___x_2892_);
lean_inc_ref_n(v___x_2888_, 2);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_2872_, v___x_2888_, v_sz_2893_, v___x_2891_, v___x_2892_);
v___x_2895_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2896_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15);
v___x_2897_ = l_Lean_mkSepArray(v___x_2894_, v___x_2896_);
lean_dec_ref(v___x_2894_);
v___x_2898_ = l_Array_append___redArg(v___x_2887_, v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2872_);
lean_ctor_set(v___x_2899_, 1, v___x_2886_);
lean_ctor_set(v___x_2899_, 2, v___x_2898_);
v___x_2900_ = l_Lean_Syntax_node1(v_a_2872_, v___x_2889_, v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16));
v___x_2902_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17));
v___x_2903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_a_2872_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = l_Lean_Syntax_node1(v_a_2872_, v___x_2886_, v___x_2903_);
v___x_2905_ = l_Lean_Syntax_node1(v_a_2872_, v___x_2901_, v___x_2904_);
v___x_2906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_3354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_a_2872_);
lean_ctor_set(v___x_3354_, 1, v___x_2906_);
v___x_3355_ = l_Lean_Syntax_node6(v_a_2872_, v___x_2883_, v___x_2885_, v___x_2888_, v___x_2900_, v___x_2905_, v___x_2888_, v___x_3354_);
v___x_3356_ = lean_array_get_size(v_views_2865_);
v___x_3357_ = lean_nat_dec_lt(v___x_2877_, v___x_3356_);
if (v___x_3357_ == 0)
{
lean_dec(v___x_3355_);
lean_dec_ref(v_views_2865_);
v_a_3322_ = v_data_2880_;
v_a_3323_ = v_a_2873_;
goto v___jp_3321_;
}
else
{
uint8_t v___x_3358_; 
v___x_3358_ = lean_nat_dec_le(v___x_3356_, v___x_3356_);
if (v___x_3358_ == 0)
{
if (v___x_3357_ == 0)
{
lean_dec(v___x_3355_);
lean_dec_ref(v_views_2865_);
v_a_3322_ = v_data_2880_;
v_a_3323_ = v_a_2873_;
goto v___jp_3321_;
}
else
{
size_t v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = lean_usize_of_nat(v___x_3356_);
lean_inc(v_vis_x3f_2861_);
lean_inc(v_structTy_2864_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2864_, v___x_3355_, v_vis_x3f_2861_, v_structId_2862_, v_views_2865_, v___x_2891_, v___x_3359_, v_data_2880_, v_a_2866_, v_a_2873_);
lean_dec_ref(v_views_2865_);
v___y_3342_ = v___x_3360_;
goto v___jp_3341_;
}
}
else
{
size_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_usize_of_nat(v___x_3356_);
lean_inc(v_vis_x3f_2861_);
lean_inc(v_structTy_2864_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2864_, v___x_3355_, v_vis_x3f_2861_, v_structId_2862_, v_views_2865_, v___x_2891_, v___x_3361_, v_data_2880_, v_a_2866_, v_a_2873_);
lean_dec_ref(v_views_2865_);
v___y_3342_ = v___x_3362_;
goto v___jp_3341_;
}
}
v___jp_2907_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2933_ = l_Array_append___redArg(v___x_2887_, v___y_2932_);
lean_dec_ref(v___y_2932_);
lean_inc_n(v___y_2928_, 27);
v___x_2934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2934_, 0, v___y_2928_);
lean_ctor_set(v___x_2934_, 1, v___x_2886_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
lean_inc_n(v___y_2919_, 16);
lean_inc(v___y_2914_);
v___x_2935_ = l_Lean_Syntax_node7(v___y_2928_, v___y_2914_, v___y_2919_, v___y_2919_, v___x_2934_, v___y_2919_, v___y_2919_, v___y_2919_, v___y_2919_);
v___x_2936_ = l_Lean_Syntax_node1(v___y_2928_, v___y_2930_, v___y_2919_);
v___x_2937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___y_2928_);
lean_ctor_set(v___x_2937_, 1, v___y_2910_);
v___x_2938_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2924_, v___y_2920_, v___y_2919_);
v___x_2939_ = l_Lean_Syntax_node1(v___y_2928_, v___x_2886_, v___x_2938_);
lean_inc_ref(v___y_2925_);
v___x_2940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2928_);
lean_ctor_set(v___x_2940_, 1, v___y_2925_);
v___x_2941_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19);
v___x_2942_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20));
lean_inc(v_currMacroScope_2869_);
lean_inc(v_quotContext_2868_);
v___x_2943_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_2942_, v_currMacroScope_2869_);
v___x_2944_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24));
v___x_2945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2945_, 0, v___y_2928_);
lean_ctor_set(v___x_2945_, 1, v___x_2941_);
lean_ctor_set(v___x_2945_, 2, v___x_2943_);
lean_ctor_set(v___x_2945_, 3, v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node1(v___y_2928_, v___x_2886_, v_structTy_2864_);
v___x_2947_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2921_, v___x_2945_, v___x_2946_);
v___x_2948_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2911_, v___x_2940_, v___x_2947_);
v___x_2949_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2917_, v___y_2919_, v___x_2948_);
lean_inc_ref(v___y_2912_);
v___x_2950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___y_2928_);
lean_ctor_set(v___x_2950_, 1, v___y_2912_);
lean_inc_ref(v___y_2909_);
v___x_2951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___y_2928_);
lean_ctor_set(v___x_2951_, 1, v___y_2909_);
v___x_2952_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26));
v___x_2953_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28));
v___x_2954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___y_2928_);
lean_ctor_set(v___x_2954_, 1, v___x_2884_);
v___x_2955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___y_2928_);
lean_ctor_set(v___x_2955_, 1, v___x_2906_);
lean_inc_ref(v___x_2955_);
lean_inc_ref(v___x_2954_);
v___x_2956_ = l_Lean_Syntax_node2(v___y_2928_, v___x_2953_, v___x_2954_, v___x_2955_);
v___x_2957_ = l_Lean_Syntax_node1(v___y_2928_, v___x_2889_, v___y_2919_);
v___x_2958_ = l_Lean_Syntax_node1(v___y_2928_, v___x_2901_, v___y_2919_);
v___x_2959_ = l_Lean_Syntax_node6(v___y_2928_, v___x_2883_, v___x_2954_, v___y_2919_, v___x_2957_, v___x_2958_, v___y_2919_, v___x_2955_);
v___x_2960_ = l_Lean_Syntax_node2(v___y_2928_, v___x_2952_, v___x_2956_, v___x_2959_);
v___x_2961_ = l_Lean_Syntax_node1(v___y_2928_, v___x_2886_, v___x_2960_);
lean_inc_ref(v___y_2929_);
v___x_2962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___y_2928_);
lean_ctor_set(v___x_2962_, 1, v___y_2929_);
v___x_2963_ = l_Lean_Syntax_node3(v___y_2928_, v___y_2915_, v___x_2951_, v___x_2961_, v___x_2962_);
v___x_2964_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2927_, v___y_2919_, v___y_2919_);
v___x_2965_ = l_Lean_Syntax_node4(v___y_2928_, v___y_2918_, v___x_2950_, v___x_2963_, v___x_2964_, v___y_2919_);
v___x_2966_ = l_Lean_Syntax_node6(v___y_2928_, v___y_2916_, v___x_2936_, v___x_2937_, v___y_2919_, v___x_2939_, v___x_2949_, v___x_2965_);
lean_inc(v___y_2923_);
v___x_2967_ = l_Lean_Syntax_node2(v___y_2928_, v___y_2923_, v___x_2935_, v___x_2966_);
v___x_2968_ = lean_array_push(v___y_2922_, v___y_2931_);
v___x_2969_ = lean_array_push(v___x_2968_, v___y_2908_);
v___x_2970_ = lean_array_push(v___x_2969_, v___y_2926_);
v___x_2971_ = lean_array_push(v___x_2970_, v___x_2967_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___y_2913_);
lean_ctor_set(v___x_2875_, 0, v___x_2971_);
v___x_2973_ = v___x_2875_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___y_2913_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
v___jp_2975_:
{
lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2998_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v___y_2977_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc_n(v_a_2999_, 2);
v_a_3000_ = lean_ctor_get(v___x_2998_, 1);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2998_);
v___x_3001_ = l_Lean_mkIdentFrom(v_structId_2862_, v___y_2997_, v___x_2878_);
lean_dec(v_structId_2862_);
v___x_3002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3002_, 0, v_a_2999_);
lean_ctor_set(v___x_3002_, 1, v___x_2886_);
lean_ctor_set(v___x_3002_, 2, v___x_2887_);
if (lean_obj_tag(v_vis_x3f_2861_) == 1)
{
lean_object* v_val_3003_; lean_object* v___x_3004_; 
v_val_3003_ = lean_ctor_get(v_vis_x3f_2861_, 0);
lean_inc(v_val_3003_);
lean_dec_ref(v_vis_x3f_2861_);
v___x_3004_ = l_Array_mkArray1___redArg(v_val_3003_);
v___y_2908_ = v___y_2976_;
v___y_2909_ = v___y_2978_;
v___y_2910_ = v___y_2979_;
v___y_2911_ = v___y_2980_;
v___y_2912_ = v___y_2981_;
v___y_2913_ = v_a_3000_;
v___y_2914_ = v___y_2982_;
v___y_2915_ = v___y_2983_;
v___y_2916_ = v___y_2984_;
v___y_2917_ = v___y_2985_;
v___y_2918_ = v___y_2986_;
v___y_2919_ = v___x_3002_;
v___y_2920_ = v___x_3001_;
v___y_2921_ = v___y_2987_;
v___y_2922_ = v___y_2988_;
v___y_2923_ = v___y_2989_;
v___y_2924_ = v___y_2991_;
v___y_2925_ = v___y_2990_;
v___y_2926_ = v___y_2992_;
v___y_2927_ = v___y_2993_;
v___y_2928_ = v_a_2999_;
v___y_2929_ = v___y_2995_;
v___y_2930_ = v___y_2994_;
v___y_2931_ = v___y_2996_;
v___y_2932_ = v___x_3004_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_3005_; 
lean_dec(v_vis_x3f_2861_);
v___x_3005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2908_ = v___y_2976_;
v___y_2909_ = v___y_2978_;
v___y_2910_ = v___y_2979_;
v___y_2911_ = v___y_2980_;
v___y_2912_ = v___y_2981_;
v___y_2913_ = v_a_3000_;
v___y_2914_ = v___y_2982_;
v___y_2915_ = v___y_2983_;
v___y_2916_ = v___y_2984_;
v___y_2917_ = v___y_2985_;
v___y_2918_ = v___y_2986_;
v___y_2919_ = v___x_3002_;
v___y_2920_ = v___x_3001_;
v___y_2921_ = v___y_2987_;
v___y_2922_ = v___y_2988_;
v___y_2923_ = v___y_2989_;
v___y_2924_ = v___y_2991_;
v___y_2925_ = v___y_2990_;
v___y_2926_ = v___y_2992_;
v___y_2927_ = v___y_2993_;
v___y_2928_ = v_a_2999_;
v___y_2929_ = v___y_2995_;
v___y_2930_ = v___y_2994_;
v___y_2931_ = v___y_2996_;
v___y_2932_ = v___x_3005_;
goto v___jp_2907_;
}
}
v___jp_3006_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3035_ = l_Array_append___redArg(v___x_2887_, v___y_3034_);
lean_dec_ref(v___y_3034_);
lean_inc_n(v___y_3028_, 16);
v___x_3036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___y_3028_);
lean_ctor_set(v___x_3036_, 1, v___x_2886_);
lean_ctor_set(v___x_3036_, 2, v___x_3035_);
lean_inc_n(v___y_3030_, 12);
lean_inc(v___y_3025_);
v___x_3037_ = l_Lean_Syntax_node7(v___y_3028_, v___y_3025_, v___y_3030_, v___y_3030_, v___x_3036_, v___y_3030_, v___y_3030_, v___y_3030_, v___y_3030_);
lean_inc(v___y_3031_);
v___x_3038_ = l_Lean_Syntax_node1(v___y_3028_, v___y_3031_, v___y_3030_);
lean_inc_ref(v___y_3009_);
v___x_3039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___y_3028_);
lean_ctor_set(v___x_3039_, 1, v___y_3009_);
lean_inc(v___y_3017_);
v___x_3040_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3017_, v___y_3032_, v___y_3030_);
v___x_3041_ = l_Lean_Syntax_node1(v___y_3028_, v___x_2886_, v___x_3040_);
lean_inc_ref(v___y_3016_);
v___x_3042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3028_);
lean_ctor_set(v___x_3042_, 1, v___y_3016_);
v___x_3043_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_3044_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30);
v___x_3045_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31));
lean_inc(v_currMacroScope_2869_);
lean_inc(v_quotContext_2868_);
v___x_3046_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_3045_, v_currMacroScope_2869_);
lean_inc_ref(v___y_3029_);
v___x_3047_ = l_Lean_Name_mkStr2(v___y_3029_, v___x_3043_);
lean_inc(v___x_3047_);
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_2879_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_2879_);
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3048_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3028_);
lean_ctor_set(v___x_3052_, 1, v___x_3044_);
lean_ctor_set(v___x_3052_, 2, v___x_3046_);
lean_ctor_set(v___x_3052_, 3, v___x_3051_);
v___x_3053_ = l_Lean_Syntax_node1(v___y_3028_, v___x_2886_, v___y_3033_);
lean_inc(v___y_3013_);
v___x_3054_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3013_, v___x_3052_, v___x_3053_);
lean_inc(v___y_3023_);
v___x_3055_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3023_, v___x_3042_, v___x_3054_);
lean_inc(v___y_3026_);
v___x_3056_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3026_, v___y_3030_, v___x_3055_);
lean_inc_ref(v___y_3010_);
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3028_);
lean_ctor_set(v___x_3057_, 1, v___y_3010_);
lean_inc(v___y_3018_);
v___x_3058_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3018_, v___y_3030_, v___y_3030_);
lean_inc(v___y_3027_);
v___x_3059_ = l_Lean_Syntax_node4(v___y_3028_, v___y_3027_, v___x_3057_, v___y_3024_, v___x_3058_, v___y_3030_);
lean_inc(v___y_3012_);
v___x_3060_ = l_Lean_Syntax_node6(v___y_3028_, v___y_3012_, v___x_3038_, v___x_3039_, v___y_3030_, v___x_3041_, v___x_3056_, v___x_3059_);
lean_inc(v___y_3015_);
v___x_3061_ = l_Lean_Syntax_node2(v___y_3028_, v___y_3015_, v___x_3037_, v___x_3060_);
v___x_3062_ = l_Lean_Name_hasMacroScopes(v___y_3007_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v___y_3007_);
v___y_2976_ = v___y_3021_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3022_;
v___y_2979_ = v___y_3009_;
v___y_2980_ = v___y_3023_;
v___y_2981_ = v___y_3010_;
v___y_2982_ = v___y_3025_;
v___y_2983_ = v___y_3011_;
v___y_2984_ = v___y_3012_;
v___y_2985_ = v___y_3026_;
v___y_2986_ = v___y_3027_;
v___y_2987_ = v___y_3013_;
v___y_2988_ = v___y_3014_;
v___y_2989_ = v___y_3015_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3017_;
v___y_2992_ = v___x_3061_;
v___y_2993_ = v___y_3018_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3019_;
v___y_2996_ = v___y_3020_;
v___y_2997_ = v___x_3063_;
goto v___jp_2975_;
}
else
{
lean_object* v_view_3064_; lean_object* v_name_3065_; lean_object* v_imported_3066_; lean_object* v_ctx_3067_; lean_object* v_scopes_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3077_; 
v_view_3064_ = l_Lean_extractMacroScopes(v___y_3007_);
v_name_3065_ = lean_ctor_get(v_view_3064_, 0);
v_imported_3066_ = lean_ctor_get(v_view_3064_, 1);
v_ctx_3067_ = lean_ctor_get(v_view_3064_, 2);
v_scopes_3068_ = lean_ctor_get(v_view_3064_, 3);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_view_3064_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3070_ = v_view_3064_;
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_scopes_3068_);
lean_inc(v_ctx_3067_);
lean_inc(v_imported_3066_);
lean_inc(v_name_3065_);
lean_dec(v_view_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3072_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v_name_3065_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3072_);
v___x_3074_ = v___x_3070_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_imported_3066_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_ctx_3067_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_scopes_3068_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_MacroScopesView_review(v___x_3074_);
v___y_2976_ = v___y_3021_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3022_;
v___y_2979_ = v___y_3009_;
v___y_2980_ = v___y_3023_;
v___y_2981_ = v___y_3010_;
v___y_2982_ = v___y_3025_;
v___y_2983_ = v___y_3011_;
v___y_2984_ = v___y_3012_;
v___y_2985_ = v___y_3026_;
v___y_2986_ = v___y_3027_;
v___y_2987_ = v___y_3013_;
v___y_2988_ = v___y_3014_;
v___y_2989_ = v___y_3015_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3017_;
v___y_2992_ = v___x_3061_;
v___y_2993_ = v___y_3018_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3019_;
v___y_2996_ = v___y_3020_;
v___y_2997_ = v___x_3075_;
goto v___jp_2975_;
}
}
}
}
v___jp_3078_:
{
lean_object* v___x_3103_; lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3154_; 
v___x_3103_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v___y_3094_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_a_3105_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3107_ = v___x_3103_;
v_isShared_3108_ = v_isSharedCheck_3154_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3154_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33));
lean_inc(v_a_3104_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set_tag(v___x_3107_, 2);
lean_ctor_set(v___x_3107_, 1, v___x_2884_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3104_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_2884_);
v___x_3111_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_a_3143_; lean_object* v_a_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_inc_n(v_a_3104_, 17);
v___x_3112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3112_, 0, v_a_3104_);
lean_ctor_set(v___x_3112_, 1, v___x_2886_);
lean_ctor_set(v___x_3112_, 2, v___x_2887_);
v___x_3113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1));
v___x_3114_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2));
v___x_3115_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34);
v___x_3116_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35));
lean_inc_n(v_currMacroScope_2869_, 2);
lean_inc_n(v_quotContext_2868_, 2);
v___x_3117_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_3116_, v_currMacroScope_2869_);
v___x_3118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3118_, 0, v_a_3104_);
lean_ctor_set(v___x_3118_, 1, v___x_3115_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
lean_ctor_set(v___x_3118_, 3, v___x_2879_);
lean_inc_ref_n(v___x_3112_, 10);
v___x_3119_ = l_Lean_Syntax_node2(v_a_3104_, v___x_3114_, v___x_3118_, v___x_3112_);
v___x_3120_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36));
lean_inc_ref(v___y_3084_);
v___x_3121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3121_, 0, v_a_3104_);
lean_ctor_set(v___x_3121_, 1, v___y_3084_);
lean_inc_ref(v___x_3121_);
v___x_3122_ = l_Lean_Syntax_node3(v_a_3104_, v___x_3120_, v___x_3121_, v___x_3112_, v___y_3101_);
v___x_3123_ = l_Lean_Syntax_node3(v_a_3104_, v___x_2886_, v___x_3112_, v___x_3112_, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_node2(v_a_3104_, v___x_3113_, v___x_3119_, v___x_3123_);
v___x_3125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3104_);
lean_ctor_set(v___x_3125_, 1, v___x_2895_);
v___x_3126_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38);
v___x_3127_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39));
v___x_3128_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_3127_, v_currMacroScope_2869_);
v___x_3129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3129_, 0, v_a_3104_);
lean_ctor_set(v___x_3129_, 1, v___x_3126_);
lean_ctor_set(v___x_3129_, 2, v___x_3128_);
lean_ctor_set(v___x_3129_, 3, v___x_2879_);
v___x_3130_ = l_Lean_Syntax_node2(v_a_3104_, v___x_3114_, v___x_3129_, v___x_3112_);
v___x_3131_ = l_Nat_reprFast(v_structArity_2863_);
v___x_3132_ = lean_box(2);
v___x_3133_ = l_Lean_Syntax_mkNumLit(v___x_3131_, v___x_3132_);
v___x_3134_ = l_Lean_Syntax_node3(v_a_3104_, v___x_3120_, v___x_3121_, v___x_3112_, v___x_3133_);
v___x_3135_ = l_Lean_Syntax_node3(v_a_3104_, v___x_2886_, v___x_3112_, v___x_3112_, v___x_3134_);
v___x_3136_ = l_Lean_Syntax_node2(v_a_3104_, v___x_3113_, v___x_3130_, v___x_3135_);
v___x_3137_ = l_Lean_Syntax_node3(v_a_3104_, v___x_2886_, v___x_3124_, v___x_3125_, v___x_3136_);
v___x_3138_ = l_Lean_Syntax_node1(v_a_3104_, v___x_2889_, v___x_3137_);
v___x_3139_ = l_Lean_Syntax_node1(v_a_3104_, v___x_2901_, v___x_3112_);
v___x_3140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3104_);
lean_ctor_set(v___x_3140_, 1, v___x_2906_);
v___x_3141_ = l_Lean_Syntax_node6(v_a_3104_, v___x_2883_, v___x_3111_, v___x_3112_, v___x_3138_, v___x_3139_, v___x_3112_, v___x_3140_);
v___x_3142_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v_a_3105_);
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_n(v_a_3143_, 2);
v_a_3144_ = lean_ctor_get(v___x_3142_, 1);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3142_);
v___x_3145_ = l_Lean_mkIdentFrom(v_structId_2862_, v___y_3102_, v___x_2878_);
v___x_3146_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43);
lean_inc(v_structId_2862_);
v___x_3147_ = lean_array_push(v___x_3146_, v_structId_2862_);
v___x_3148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3132_);
lean_ctor_set(v___x_3148_, 1, v___x_3109_);
lean_ctor_set(v___x_3148_, 2, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3149_, 0, v_a_3143_);
lean_ctor_set(v___x_3149_, 1, v___x_2886_);
lean_ctor_set(v___x_3149_, 2, v___x_2887_);
if (lean_obj_tag(v_vis_x3f_2861_) == 1)
{
lean_object* v_val_3150_; lean_object* v___x_3151_; 
v_val_3150_ = lean_ctor_get(v_vis_x3f_2861_, 0);
lean_inc(v_val_3150_);
v___x_3151_ = l_Array_mkArray1___redArg(v_val_3150_);
v___y_3007_ = v___y_3079_;
v___y_3008_ = v_a_3144_;
v___y_3009_ = v___y_3083_;
v___y_3010_ = v___y_3084_;
v___y_3011_ = v___y_3086_;
v___y_3012_ = v___y_3088_;
v___y_3013_ = v___y_3090_;
v___y_3014_ = v___y_3091_;
v___y_3015_ = v___y_3093_;
v___y_3016_ = v___y_3095_;
v___y_3017_ = v___y_3096_;
v___y_3018_ = v___y_3097_;
v___y_3019_ = v___y_3099_;
v___y_3020_ = v___y_3100_;
v___y_3021_ = v___y_3080_;
v___y_3022_ = v___y_3081_;
v___y_3023_ = v___y_3082_;
v___y_3024_ = v___x_3141_;
v___y_3025_ = v___y_3085_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3089_;
v___y_3028_ = v_a_3143_;
v___y_3029_ = v___y_3092_;
v___y_3030_ = v___x_3149_;
v___y_3031_ = v___y_3098_;
v___y_3032_ = v___x_3145_;
v___y_3033_ = v___x_3148_;
v___y_3034_ = v___x_3151_;
goto v___jp_3006_;
}
else
{
lean_object* v___x_3152_; 
v___x_3152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3007_ = v___y_3079_;
v___y_3008_ = v_a_3144_;
v___y_3009_ = v___y_3083_;
v___y_3010_ = v___y_3084_;
v___y_3011_ = v___y_3086_;
v___y_3012_ = v___y_3088_;
v___y_3013_ = v___y_3090_;
v___y_3014_ = v___y_3091_;
v___y_3015_ = v___y_3093_;
v___y_3016_ = v___y_3095_;
v___y_3017_ = v___y_3096_;
v___y_3018_ = v___y_3097_;
v___y_3019_ = v___y_3099_;
v___y_3020_ = v___y_3100_;
v___y_3021_ = v___y_3080_;
v___y_3022_ = v___y_3081_;
v___y_3023_ = v___y_3082_;
v___y_3024_ = v___x_3141_;
v___y_3025_ = v___y_3085_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3089_;
v___y_3028_ = v_a_3143_;
v___y_3029_ = v___y_3092_;
v___y_3030_ = v___x_3149_;
v___y_3031_ = v___y_3098_;
v___y_3032_ = v___x_3145_;
v___y_3033_ = v___x_3148_;
v___y_3034_ = v___x_3152_;
goto v___jp_3006_;
}
}
}
}
v___jp_3155_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3172_ = l_Array_append___redArg(v___x_2887_, v___y_3171_);
lean_dec_ref(v___y_3171_);
lean_inc_n(v___y_3161_, 20);
v___x_3173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3161_);
lean_ctor_set(v___x_3173_, 1, v___x_2886_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
lean_inc_n(v___y_3160_, 12);
lean_inc(v___y_3159_);
v___x_3174_ = l_Lean_Syntax_node7(v___y_3161_, v___y_3159_, v___y_3160_, v___y_3160_, v___x_3173_, v___y_3160_, v___y_3160_, v___y_3160_, v___y_3160_);
v___x_3175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_3157_, 2);
v___x_3176_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3157_, v___x_3175_);
v___x_3177_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44));
v___x_3178_ = l_Lean_Syntax_node1(v___y_3161_, v___x_3177_, v___y_3160_);
v___x_3179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___y_3161_);
lean_ctor_set(v___x_3179_, 1, v___x_3175_);
lean_inc(v___y_3166_);
v___x_3180_ = l_Lean_Syntax_node2(v___y_3161_, v___y_3166_, v___y_3167_, v___y_3160_);
v___x_3181_ = l_Lean_Syntax_node1(v___y_3161_, v___x_2886_, v___x_3180_);
v___x_3182_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_3183_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3157_, v___x_3182_);
v___x_3184_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
v___x_3185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___y_3161_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
v___x_3188_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47);
v___x_3189_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48));
lean_inc(v_currMacroScope_2869_);
lean_inc(v_quotContext_2868_);
v___x_3190_ = l_Lean_addMacroScope(v_quotContext_2868_, v___x_3189_, v_currMacroScope_2869_);
v___x_3191_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_3192_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53));
v___x_3193_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3193_, 0, v___y_3161_);
lean_ctor_set(v___x_3193_, 1, v___x_3188_);
lean_ctor_set(v___x_3193_, 2, v___x_3190_);
lean_ctor_set(v___x_3193_, 3, v___x_3192_);
lean_inc(v_structTy_2864_);
v___x_3194_ = l_Lean_Syntax_node1(v___y_3161_, v___x_2886_, v_structTy_2864_);
v___x_3195_ = l_Lean_Syntax_node2(v___y_3161_, v___x_3187_, v___x_3193_, v___x_3194_);
v___x_3196_ = l_Lean_Syntax_node2(v___y_3161_, v___x_3184_, v___x_3186_, v___x_3195_);
lean_inc(v___x_3183_);
v___x_3197_ = l_Lean_Syntax_node2(v___y_3161_, v___x_3183_, v___y_3160_, v___x_3196_);
lean_inc_ref(v___y_3158_);
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3161_);
lean_ctor_set(v___x_3198_, 1, v___y_3158_);
v___x_3199_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54));
v___x_3200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3161_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
lean_inc(v___y_3170_);
v___x_3202_ = l_Lean_Syntax_node1(v___y_3161_, v___x_2886_, v___y_3170_);
v___x_3203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_3204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3161_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = l_Lean_Syntax_node3(v___y_3161_, v___x_3199_, v___x_3201_, v___x_3202_, v___x_3204_);
lean_inc(v___y_3168_);
v___x_3206_ = l_Lean_Syntax_node2(v___y_3161_, v___y_3168_, v___y_3160_, v___y_3160_);
lean_inc(v___y_3162_);
v___x_3207_ = l_Lean_Syntax_node4(v___y_3161_, v___y_3162_, v___x_3198_, v___x_3205_, v___x_3206_, v___y_3160_);
lean_inc(v___x_3176_);
v___x_3208_ = l_Lean_Syntax_node6(v___y_3161_, v___x_3176_, v___x_3178_, v___x_3179_, v___y_3160_, v___x_3181_, v___x_3197_, v___x_3207_);
lean_inc(v___y_3164_);
v___x_3209_ = l_Lean_Syntax_node2(v___y_3161_, v___y_3164_, v___x_3174_, v___x_3208_);
v___x_3210_ = l_Lean_Name_hasMacroScopes(v___y_3156_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_inc(v___y_3156_);
v___x_3211_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v___y_3156_);
v___y_3079_ = v___y_3156_;
v___y_3080_ = v___x_3209_;
v___y_3081_ = v___x_3200_;
v___y_3082_ = v___x_3184_;
v___y_3083_ = v___x_3175_;
v___y_3084_ = v___y_3158_;
v___y_3085_ = v___y_3159_;
v___y_3086_ = v___x_3199_;
v___y_3087_ = v___x_3183_;
v___y_3088_ = v___x_3176_;
v___y_3089_ = v___y_3162_;
v___y_3090_ = v___x_3187_;
v___y_3091_ = v___y_3163_;
v___y_3092_ = v___x_3191_;
v___y_3093_ = v___y_3164_;
v___y_3094_ = v___y_3165_;
v___y_3095_ = v___x_3185_;
v___y_3096_ = v___y_3166_;
v___y_3097_ = v___y_3168_;
v___y_3098_ = v___x_3177_;
v___y_3099_ = v___x_3203_;
v___y_3100_ = v___y_3169_;
v___y_3101_ = v___y_3170_;
v___y_3102_ = v___x_3211_;
goto v___jp_3078_;
}
else
{
lean_object* v_view_3212_; lean_object* v_name_3213_; lean_object* v_imported_3214_; lean_object* v_ctx_3215_; lean_object* v_scopes_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3225_; 
lean_inc(v___y_3156_);
v_view_3212_ = l_Lean_extractMacroScopes(v___y_3156_);
v_name_3213_ = lean_ctor_get(v_view_3212_, 0);
v_imported_3214_ = lean_ctor_get(v_view_3212_, 1);
v_ctx_3215_ = lean_ctor_get(v_view_3212_, 2);
v_scopes_3216_ = lean_ctor_get(v_view_3212_, 3);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_view_3212_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3218_ = v_view_3212_;
v_isShared_3219_ = v_isSharedCheck_3225_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_scopes_3216_);
lean_inc(v_ctx_3215_);
lean_inc(v_imported_3214_);
lean_inc(v_name_3213_);
lean_dec(v_view_3212_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3225_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v_name_3213_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_imported_3214_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_ctx_3215_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_scopes_3216_);
v___x_3222_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Lean_MacroScopesView_review(v___x_3222_);
v___y_3079_ = v___y_3156_;
v___y_3080_ = v___x_3209_;
v___y_3081_ = v___x_3200_;
v___y_3082_ = v___x_3184_;
v___y_3083_ = v___x_3175_;
v___y_3084_ = v___y_3158_;
v___y_3085_ = v___y_3159_;
v___y_3086_ = v___x_3199_;
v___y_3087_ = v___x_3183_;
v___y_3088_ = v___x_3176_;
v___y_3089_ = v___y_3162_;
v___y_3090_ = v___x_3187_;
v___y_3091_ = v___y_3163_;
v___y_3092_ = v___x_3191_;
v___y_3093_ = v___y_3164_;
v___y_3094_ = v___y_3165_;
v___y_3095_ = v___x_3185_;
v___y_3096_ = v___y_3166_;
v___y_3097_ = v___y_3168_;
v___y_3098_ = v___x_3177_;
v___y_3099_ = v___x_3203_;
v___y_3100_ = v___y_3169_;
v___y_3101_ = v___y_3170_;
v___y_3102_ = v___x_3223_;
goto v___jp_3078_;
}
}
}
}
v___jp_3226_:
{
lean_object* v___x_3240_; lean_object* v_a_3241_; lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3240_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v___y_3236_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc_n(v_a_3241_, 2);
v_a_3242_ = lean_ctor_get(v___x_3240_, 1);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3240_);
v___x_3243_ = l_Lean_mkIdentFrom(v_structId_2862_, v___y_3239_, v___x_2878_);
v___x_3244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3244_, 0, v_a_3241_);
lean_ctor_set(v___x_3244_, 1, v___x_2886_);
lean_ctor_set(v___x_3244_, 2, v___x_2887_);
if (lean_obj_tag(v_vis_x3f_2861_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3246_; 
v_val_3245_ = lean_ctor_get(v_vis_x3f_2861_, 0);
lean_inc(v_val_3245_);
v___x_3246_ = l_Array_mkArray1___redArg(v_val_3245_);
v___y_3156_ = v___y_3228_;
v___y_3157_ = v___y_3232_;
v___y_3158_ = v___y_3234_;
v___y_3159_ = v___y_3235_;
v___y_3160_ = v___x_3244_;
v___y_3161_ = v_a_3241_;
v___y_3162_ = v___y_3238_;
v___y_3163_ = v___y_3227_;
v___y_3164_ = v___y_3229_;
v___y_3165_ = v_a_3242_;
v___y_3166_ = v___y_3230_;
v___y_3167_ = v___x_3243_;
v___y_3168_ = v___y_3231_;
v___y_3169_ = v___y_3233_;
v___y_3170_ = v___y_3237_;
v___y_3171_ = v___x_3246_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3247_; 
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3156_ = v___y_3228_;
v___y_3157_ = v___y_3232_;
v___y_3158_ = v___y_3234_;
v___y_3159_ = v___y_3235_;
v___y_3160_ = v___x_3244_;
v___y_3161_ = v_a_3241_;
v___y_3162_ = v___y_3238_;
v___y_3163_ = v___y_3227_;
v___y_3164_ = v___y_3229_;
v___y_3165_ = v_a_3242_;
v___y_3166_ = v___y_3230_;
v___y_3167_ = v___x_3243_;
v___y_3168_ = v___y_3231_;
v___y_3169_ = v___y_3233_;
v___y_3170_ = v___y_3237_;
v___y_3171_ = v___x_3247_;
goto v___jp_3155_;
}
}
v___jp_3248_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v_cmds_3272_; lean_object* v_fields_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3304_; 
v___x_3259_ = l_Array_append___redArg(v___x_2887_, v___y_3258_);
lean_dec_ref(v___y_3258_);
lean_inc_n(v___y_3252_, 5);
v___x_3260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3260_, 0, v___y_3252_);
lean_ctor_set(v___x_3260_, 1, v___x_2886_);
lean_ctor_set(v___x_3260_, 2, v___x_3259_);
lean_inc_n(v___y_3253_, 9);
lean_inc(v___y_3255_);
v___x_3261_ = l_Lean_Syntax_node7(v___y_3252_, v___y_3255_, v___y_3253_, v___y_3253_, v___x_3260_, v___y_3253_, v___y_3253_, v___y_3253_, v___y_3253_);
v___x_3262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_3254_, 3);
v___x_3263_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3254_, v___x_3262_);
v___x_3264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_3265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___y_3252_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_3267_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3254_, v___x_3266_);
lean_inc(v___y_3257_);
lean_inc(v___x_3267_);
v___x_3268_ = l_Lean_Syntax_node2(v___y_3252_, v___x_3267_, v___y_3257_, v___y_3253_);
v___x_3269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_3270_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3254_, v___x_3269_);
v___x_3271_ = l_Lean_Syntax_node2(v___y_3252_, v___x_3270_, v___y_3253_, v___y_3253_);
v_cmds_3272_ = lean_ctor_get(v___y_3249_, 0);
v_fields_3273_ = lean_ctor_get(v___y_3249_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3275_ = v___y_3249_;
v_isShared_3276_ = v_isSharedCheck_3304_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_fields_3273_);
lean_inc(v_cmds_3272_);
lean_dec(v___y_3249_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3304_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
lean_inc_ref(v___y_3254_);
v___x_3278_ = l_Lean_Name_mkStr4(v___x_2881_, v___x_2882_, v___y_3254_, v___x_3277_);
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
lean_inc(v___y_3252_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 2);
lean_ctor_set(v___x_3275_, 1, v___x_3279_);
lean_ctor_set(v___x_3275_, 0, v___y_3252_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___y_3252_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3282_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55));
lean_inc_n(v___y_3253_, 3);
lean_inc_n(v___y_3252_, 3);
v___x_3283_ = l_Lean_Syntax_node2(v___y_3252_, v___x_3282_, v___y_3253_, v___y_3253_);
lean_inc(v___x_3278_);
v___x_3284_ = l_Lean_Syntax_node4(v___y_3252_, v___x_3278_, v___x_3281_, v_fields_3273_, v___x_3283_, v___y_3253_);
v___x_3285_ = l_Lean_Syntax_node5(v___y_3252_, v___x_3263_, v___x_3265_, v___x_3268_, v___x_3271_, v___x_3284_, v___y_3253_);
lean_inc(v___y_3251_);
v___x_3286_ = l_Lean_Syntax_node2(v___y_3252_, v___y_3251_, v___x_3261_, v___x_3285_);
v___x_3287_ = l_Lean_Name_hasMacroScopes(v___y_3250_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_inc(v___y_3250_);
v___x_3288_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v___y_3250_);
v___y_3227_ = v_cmds_3272_;
v___y_3228_ = v___y_3250_;
v___y_3229_ = v___y_3251_;
v___y_3230_ = v___x_3267_;
v___y_3231_ = v___x_3282_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___x_3286_;
v___y_3234_ = v___x_3279_;
v___y_3235_ = v___y_3255_;
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3257_;
v___y_3238_ = v___x_3278_;
v___y_3239_ = v___x_3288_;
goto v___jp_3226_;
}
else
{
lean_object* v_view_3289_; lean_object* v_name_3290_; lean_object* v_imported_3291_; lean_object* v_ctx_3292_; lean_object* v_scopes_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3302_; 
lean_inc(v___y_3250_);
v_view_3289_ = l_Lean_extractMacroScopes(v___y_3250_);
v_name_3290_ = lean_ctor_get(v_view_3289_, 0);
v_imported_3291_ = lean_ctor_get(v_view_3289_, 1);
v_ctx_3292_ = lean_ctor_get(v_view_3289_, 2);
v_scopes_3293_ = lean_ctor_get(v_view_3289_, 3);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_view_3289_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3295_ = v_view_3289_;
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_scopes_3293_);
lean_inc(v_ctx_3292_);
lean_inc(v_imported_3291_);
lean_inc(v_name_3290_);
lean_dec(v_view_3289_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v_name_3290_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3297_);
v___x_3299_ = v___x_3295_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_imported_3291_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_ctx_3292_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_scopes_3293_);
v___x_3299_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_MacroScopesView_review(v___x_3299_);
v___y_3227_ = v_cmds_3272_;
v___y_3228_ = v___y_3250_;
v___y_3229_ = v___y_3251_;
v___y_3230_ = v___x_3267_;
v___y_3231_ = v___x_3282_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___x_3286_;
v___y_3234_ = v___x_3279_;
v___y_3235_ = v___y_3255_;
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3257_;
v___y_3238_ = v___x_3278_;
v___y_3239_ = v___x_3300_;
goto v___jp_3226_;
}
}
}
}
}
}
v___jp_3305_:
{
lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3310_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2870_, v_a_2866_, v___y_3308_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc_n(v_a_3311_, 2);
v_a_3312_ = lean_ctor_get(v___x_3310_, 1);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3310_);
v___x_3313_ = l_Lean_mkIdentFrom(v_structId_2862_, v___y_3309_, v___x_2878_);
v___x_3314_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_3315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_3316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3317_, 0, v_a_3311_);
lean_ctor_set(v___x_3317_, 1, v___x_2886_);
lean_ctor_set(v___x_3317_, 2, v___x_2887_);
if (lean_obj_tag(v_vis_x3f_2861_) == 1)
{
lean_object* v_val_3318_; lean_object* v___x_3319_; 
v_val_3318_ = lean_ctor_get(v_vis_x3f_2861_, 0);
lean_inc(v_val_3318_);
v___x_3319_ = l_Array_mkArray1___redArg(v_val_3318_);
v___y_3249_ = v___y_3306_;
v___y_3250_ = v___y_3307_;
v___y_3251_ = v___x_3315_;
v___y_3252_ = v_a_3311_;
v___y_3253_ = v___x_3317_;
v___y_3254_ = v___x_3314_;
v___y_3255_ = v___x_3316_;
v___y_3256_ = v_a_3312_;
v___y_3257_ = v___x_3313_;
v___y_3258_ = v___x_3319_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3249_ = v___y_3306_;
v___y_3250_ = v___y_3307_;
v___y_3251_ = v___x_3315_;
v___y_3252_ = v_a_3311_;
v___y_3253_ = v___x_3317_;
v___y_3254_ = v___x_3314_;
v___y_3255_ = v___x_3316_;
v___y_3256_ = v_a_3312_;
v___y_3257_ = v___x_3313_;
v___y_3258_ = v___x_3320_;
goto v___jp_3248_;
}
}
v___jp_3321_:
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = l_Lean_TSyntax_getId(v_structId_2862_);
v___x_3325_ = l_Lean_Name_hasMacroScopes(v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_inc(v___x_3324_);
v___x_3326_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v___x_3324_);
v___y_3306_ = v_a_3322_;
v___y_3307_ = v___x_3324_;
v___y_3308_ = v_a_3323_;
v___y_3309_ = v___x_3326_;
goto v___jp_3305_;
}
else
{
lean_object* v_view_3327_; lean_object* v_name_3328_; lean_object* v_imported_3329_; lean_object* v_ctx_3330_; lean_object* v_scopes_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3340_; 
lean_inc(v___x_3324_);
v_view_3327_ = l_Lean_extractMacroScopes(v___x_3324_);
v_name_3328_ = lean_ctor_get(v_view_3327_, 0);
v_imported_3329_ = lean_ctor_get(v_view_3327_, 1);
v_ctx_3330_ = lean_ctor_get(v_view_3327_, 2);
v_scopes_3331_ = lean_ctor_get(v_view_3327_, 3);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_view_3327_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3333_ = v_view_3327_;
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_scopes_3331_);
lean_inc(v_ctx_3330_);
lean_inc(v_imported_3329_);
lean_inc(v_name_3328_);
lean_dec(v_view_3327_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v_name_3328_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_imported_3329_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_ctx_3330_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_scopes_3331_);
v___x_3337_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_MacroScopesView_review(v___x_3337_);
v___y_3306_ = v_a_3322_;
v___y_3307_ = v___x_3324_;
v___y_3308_ = v_a_3323_;
v___y_3309_ = v___x_3338_;
goto v___jp_3305_;
}
}
}
}
v___jp_3341_:
{
if (lean_obj_tag(v___y_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v_a_3344_; 
v_a_3343_ = lean_ctor_get(v___y_3342_, 0);
lean_inc(v_a_3343_);
v_a_3344_ = lean_ctor_get(v___y_3342_, 1);
lean_inc(v_a_3344_);
lean_dec_ref(v___y_3342_);
v_a_3322_ = v_a_3343_;
v_a_3323_ = v_a_3344_;
goto v___jp_3321_;
}
else
{
lean_object* v_a_3345_; lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_del_object(v___x_2875_);
lean_dec(v_structTy_2864_);
lean_dec(v_structArity_2863_);
lean_dec(v_structId_2862_);
lean_dec(v_vis_x3f_2861_);
v_a_3345_ = lean_ctor_get(v___y_3342_, 0);
v_a_3346_ = lean_ctor_get(v___y_3342_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___y_3342_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___y_3342_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_inc(v_a_3345_);
lean_dec(v___y_3342_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3345_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___boxed(lean_object* v_vis_x3f_3364_, lean_object* v_structId_3365_, lean_object* v_structArity_3366_, lean_object* v_structTy_3367_, lean_object* v_views_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v_vis_x3f_3364_, v_structId_3365_, v_structArity_3366_, v_structTy_3367_, v_views_3368_, v_a_3369_, v_a_3370_);
lean_dec_ref(v_a_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(size_t v_sz_3372_, size_t v_i_3373_, lean_object* v_bs_3374_){
_start:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_usize_dec_lt(v_i_3373_, v_sz_3372_);
if (v___x_3375_ == 0)
{
return v_bs_3374_;
}
else
{
lean_object* v_v_3376_; lean_object* v_id_3377_; lean_object* v___x_3378_; lean_object* v_bs_x27_3379_; size_t v___x_3380_; size_t v___x_3381_; lean_object* v___x_3382_; 
v_v_3376_ = lean_array_uget_borrowed(v_bs_3374_, v_i_3373_);
v_id_3377_ = lean_ctor_get(v_v_3376_, 1);
lean_inc(v_id_3377_);
v___x_3378_ = lean_unsigned_to_nat(0u);
v_bs_x27_3379_ = lean_array_uset(v_bs_3374_, v_i_3373_, v___x_3378_);
v___x_3380_ = ((size_t)1ULL);
v___x_3381_ = lean_usize_add(v_i_3373_, v___x_3380_);
v___x_3382_ = lean_array_uset(v_bs_x27_3379_, v_i_3373_, v_id_3377_);
v_i_3373_ = v___x_3381_;
v_bs_3374_ = v___x_3382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0___boxed(lean_object* v_sz_3384_, lean_object* v_i_3385_, lean_object* v_bs_3386_){
_start:
{
size_t v_sz_boxed_3387_; size_t v_i_boxed_3388_; lean_object* v_res_3389_; 
v_sz_boxed_3387_ = lean_unbox_usize(v_sz_3384_);
lean_dec(v_sz_3384_);
v_i_boxed_3388_ = lean_unbox_usize(v_i_3385_);
lean_dec(v_i_3385_);
v_res_3389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_boxed_3387_, v_i_boxed_3388_, v_bs_3386_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView(lean_object* v_stx_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_methods_3413_; lean_object* v_quotContext_3414_; lean_object* v_currMacroScope_3415_; lean_object* v_currRecDepth_3416_; lean_object* v_maxRecDepth_3417_; lean_object* v_ref_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v_ref_3421_; lean_object* v___x_3422_; 
v_methods_3413_ = lean_ctor_get(v_a_3411_, 0);
v_quotContext_3414_ = lean_ctor_get(v_a_3411_, 1);
v_currMacroScope_3415_ = lean_ctor_get(v_a_3411_, 2);
v_currRecDepth_3416_ = lean_ctor_get(v_a_3411_, 3);
v_maxRecDepth_3417_ = lean_ctor_get(v_a_3411_, 4);
v_ref_3418_ = lean_ctor_get(v_a_3411_, 5);
v___x_3419_ = ((lean_object*)(l_Lake_configField___closed__2));
lean_inc(v_stx_3410_);
v___x_3420_ = l_Lean_Syntax_isOfKind(v_stx_3410_, v___x_3419_);
v_ref_3421_ = l_Lean_replaceRef(v_stx_3410_, v_ref_3418_);
lean_inc(v_maxRecDepth_3417_);
lean_inc(v_currRecDepth_3416_);
lean_inc(v_currMacroScope_3415_);
lean_inc(v_quotContext_3414_);
lean_inc(v_methods_3413_);
v___x_3422_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3422_, 0, v_methods_3413_);
lean_ctor_set(v___x_3422_, 1, v_quotContext_3414_);
lean_ctor_set(v___x_3422_, 2, v_currMacroScope_3415_);
lean_ctor_set(v___x_3422_, 3, v_currRecDepth_3416_);
lean_ctor_set(v___x_3422_, 4, v_maxRecDepth_3417_);
lean_ctor_set(v___x_3422_, 5, v_ref_3421_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec(v_stx_3410_);
v___x_3423_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3424_ = l_Lean_Macro_throwError___redArg(v___x_3423_, v___x_3422_, v_a_3412_);
lean_dec_ref(v___x_3422_);
return v___x_3424_;
}
else
{
lean_object* v___x_3425_; lean_object* v_mods_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v_val_3438_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v_val_x3f_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3425_ = lean_unsigned_to_nat(0u);
v_mods_3426_ = l_Lean_Syntax_getArg(v_stx_3410_, v___x_3425_);
v___x_3427_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_3428_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_3531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v_mods_3426_);
v___x_3532_ = l_Lean_Syntax_isOfKind(v_mods_3426_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3533_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3534_ = l_Lean_Macro_throwError___redArg(v___x_3533_, v___x_3422_, v_a_3412_);
lean_dec_ref(v___x_3422_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v_id_x3f_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3565_ = l_Lean_Syntax_getArg(v_stx_3410_, v___x_3535_);
v___x_3566_ = l_Lean_Syntax_isNone(v___x_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3565_);
v___x_3568_ = l_Lean_Syntax_matchesNull(v___x_3565_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v___x_3565_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3569_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3570_ = l_Lean_Macro_throwError___redArg(v___x_3569_, v___x_3422_, v_a_3412_);
lean_dec_ref(v___x_3422_);
return v___x_3570_;
}
else
{
lean_object* v_id_x3f_3571_; lean_object* v___x_3572_; 
v_id_x3f_3571_ = l_Lean_Syntax_getArg(v___x_3565_, v___x_3425_);
lean_dec(v___x_3565_);
v___x_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3572_, 0, v_id_x3f_3571_);
v_id_x3f_3537_ = v___x_3572_;
v___y_3538_ = v___x_3422_;
v___y_3539_ = v_a_3412_;
goto v___jp_3536_;
}
}
else
{
lean_object* v___x_3573_; 
lean_dec(v___x_3565_);
v___x_3573_ = lean_box(0);
v_id_x3f_3537_ = v___x_3573_;
v___y_3538_ = v___x_3422_;
v___y_3539_ = v_a_3412_;
goto v___jp_3536_;
}
v___jp_3536_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3540_ = lean_unsigned_to_nat(3u);
v___x_3541_ = l_Lean_Syntax_getArg(v_stx_3410_, v___x_3540_);
v___x_3542_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7));
lean_inc(v___x_3541_);
v___x_3543_ = l_Lean_Syntax_isOfKind(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v___x_3541_);
lean_dec(v_id_x3f_3537_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3544_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3545_ = l_Lean_Macro_throwError___redArg(v___x_3544_, v___y_3538_, v___y_3539_);
lean_dec_ref(v___y_3538_);
return v___x_3545_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3546_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3535_);
v___x_3547_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_3548_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
lean_inc(v___x_3546_);
v___x_3549_ = l_Lean_Syntax_isOfKind(v___x_3546_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v___x_3546_);
lean_dec(v___x_3541_);
lean_dec(v_id_x3f_3537_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3550_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3551_ = l_Lean_Macro_throwError___redArg(v___x_3550_, v___y_3538_, v___y_3539_);
lean_dec_ref(v___y_3538_);
return v___x_3551_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v_rty_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3552_ = lean_unsigned_to_nat(2u);
v___x_3553_ = l_Lean_Syntax_getArg(v_stx_3410_, v___x_3552_);
v___x_3554_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3425_);
lean_dec(v___x_3541_);
v_rty_3555_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_3535_);
lean_dec(v___x_3546_);
v___x_3556_ = lean_unsigned_to_nat(4u);
v___x_3557_ = l_Lean_Syntax_getArg(v_stx_3410_, v___x_3556_);
v___x_3558_ = l_Lean_Syntax_isNone(v___x_3557_);
if (v___x_3558_ == 0)
{
uint8_t v___x_3559_; 
lean_inc(v___x_3557_);
v___x_3559_ = l_Lean_Syntax_matchesNull(v___x_3557_, v___x_3552_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v___x_3557_);
lean_dec(v_rty_3555_);
lean_dec(v___x_3554_);
lean_dec(v___x_3553_);
lean_dec(v_id_x3f_3537_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3560_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3561_ = l_Lean_Macro_throwError___redArg(v___x_3560_, v___y_3538_, v___y_3539_);
lean_dec_ref(v___y_3538_);
return v___x_3561_;
}
else
{
lean_object* v_val_x3f_3562_; lean_object* v___x_3563_; 
v_val_x3f_3562_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3535_);
lean_dec(v___x_3557_);
v___x_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_val_x3f_3562_);
v___y_3500_ = v_id_x3f_3537_;
v___y_3501_ = v_rty_3555_;
v___y_3502_ = v___x_3547_;
v___y_3503_ = v___x_3553_;
v___y_3504_ = v___x_3548_;
v___y_3505_ = v___x_3554_;
v_val_x3f_3506_ = v___x_3563_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3539_;
goto v___jp_3499_;
}
}
else
{
lean_object* v___x_3564_; 
lean_dec(v___x_3557_);
v___x_3564_ = lean_box(0);
v___y_3500_ = v_id_x3f_3537_;
v___y_3501_ = v_rty_3555_;
v___y_3502_ = v___x_3547_;
v___y_3503_ = v___x_3553_;
v___y_3504_ = v___x_3548_;
v___y_3505_ = v___x_3554_;
v_val_x3f_3506_ = v___x_3564_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3539_;
goto v___jp_3499_;
}
}
}
}
}
v___jp_3429_:
{
lean_object* v_methods_3439_; lean_object* v_quotContext_3440_; lean_object* v_currMacroScope_3441_; lean_object* v_currRecDepth_3442_; lean_object* v_maxRecDepth_3443_; lean_object* v_ref_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3498_; 
v_methods_3439_ = lean_ctor_get(v___y_3433_, 0);
v_quotContext_3440_ = lean_ctor_get(v___y_3433_, 1);
v_currMacroScope_3441_ = lean_ctor_get(v___y_3433_, 2);
v_currRecDepth_3442_ = lean_ctor_get(v___y_3433_, 3);
v_maxRecDepth_3443_ = lean_ctor_get(v___y_3433_, 4);
v_ref_3444_ = lean_ctor_get(v___y_3433_, 5);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___y_3433_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3446_ = v___y_3433_;
v_isShared_3447_ = v_isSharedCheck_3498_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_ref_3444_);
lean_inc(v_maxRecDepth_3443_);
lean_inc(v_currRecDepth_3442_);
lean_inc(v_currMacroScope_3441_);
lean_inc(v_quotContext_3440_);
lean_inc(v_methods_3439_);
lean_dec(v___y_3433_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3498_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_ref_3448_; 
v_ref_3448_ = l_Lean_replaceRef(v_val_3438_, v_ref_3444_);
lean_dec(v_ref_3444_);
if (lean_obj_tag(v___y_3435_) == 1)
{
lean_object* v_val_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3492_; 
lean_del_object(v___x_3446_);
lean_dec(v_maxRecDepth_3443_);
lean_dec(v_currRecDepth_3442_);
lean_dec(v_currMacroScope_3441_);
lean_dec(v_quotContext_3440_);
lean_dec(v_methods_3439_);
v_val_3449_ = lean_ctor_get(v___y_3435_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___y_3435_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3451_ = v___y_3435_;
v_isShared_3452_ = v_isSharedCheck_3492_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_val_3449_);
lean_dec(v___y_3435_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3492_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; size_t v_sz_3462_; size_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3453_ = 0;
v___x_3454_ = l_Lean_SourceInfo_fromRef(v_ref_3448_, v___x_3453_);
lean_dec(v_ref_3448_);
v___x_3455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
lean_inc_ref_n(v___y_3432_, 3);
v___x_3456_ = l_Lean_Name_mkStr4(v___x_3427_, v___x_3428_, v___y_3432_, v___x_3455_);
lean_inc_n(v___x_3454_, 13);
v___x_3457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3454_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_3459_ = l_Lean_Name_mkStr4(v___x_3427_, v___x_3428_, v___y_3432_, v___x_3458_);
v___x_3460_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_3461_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_3462_ = lean_array_size(v___y_3436_);
v___x_3463_ = ((size_t)0ULL);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_3462_, v___x_3463_, v___y_3436_);
v___x_3465_ = l_Array_append___redArg(v___x_3461_, v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3454_);
lean_ctor_set(v___x_3466_, 1, v___x_3460_);
lean_ctor_set(v___x_3466_, 2, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3454_);
lean_ctor_set(v___x_3467_, 1, v___x_3460_);
lean_ctor_set(v___x_3467_, 2, v___x_3461_);
v___x_3468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_3469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3454_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
lean_inc_ref(v___x_3467_);
v___x_3470_ = l_Lean_Syntax_node4(v___x_3454_, v___x_3459_, v___x_3466_, v___x_3467_, v___x_3469_, v_val_3449_);
v___x_3471_ = l_Lean_Syntax_node2(v___x_3454_, v___x_3456_, v___x_3457_, v___x_3470_);
v___x_3472_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2));
v___x_3473_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_3474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3454_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
lean_inc(v___y_3437_);
lean_inc(v___y_3434_);
v___x_3476_ = l_Lean_Syntax_node2(v___x_3454_, v___y_3434_, v___x_3475_, v___y_3437_);
v___x_3477_ = l_Lean_Syntax_node1(v___x_3454_, v___x_3460_, v___x_3476_);
v___x_3478_ = l_Lean_Syntax_node2(v___x_3454_, v___x_3473_, v___x_3467_, v___x_3477_);
v___x_3479_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4));
v___x_3480_ = l_Lean_Name_mkStr4(v___x_3427_, v___x_3428_, v___y_3432_, v___x_3479_);
v___x_3481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_3482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3454_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_inc(v___x_3471_);
v___x_3483_ = l_Lean_Syntax_node2(v___x_3454_, v___x_3480_, v___x_3482_, v___x_3471_);
v___x_3484_ = l_Lean_Syntax_node1(v___x_3454_, v___x_3460_, v___x_3483_);
lean_inc(v_val_3438_);
lean_inc(v_mods_3426_);
v___x_3485_ = l_Lean_Syntax_node4(v___x_3454_, v___x_3472_, v_mods_3426_, v_val_3438_, v___x_3478_, v___x_3484_);
v___x_3486_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_3431_);
lean_dec_ref(v___y_3431_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3485_);
v___x_3488_ = v___x_3451_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3485_);
v___x_3488_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3489_, 0, v_stx_3410_);
lean_ctor_set(v___x_3489_, 1, v_mods_3426_);
lean_ctor_set(v___x_3489_, 2, v_val_3438_);
lean_ctor_set(v___x_3489_, 3, v___x_3486_);
lean_ctor_set(v___x_3489_, 4, v___y_3437_);
lean_ctor_set(v___x_3489_, 5, v___x_3471_);
lean_ctor_set(v___x_3489_, 6, v___x_3488_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*7, v___x_3453_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___y_3430_);
return v___x_3490_;
}
}
}
else
{
lean_object* v___x_3494_; 
lean_dec(v_val_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3431_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 5, v_ref_3448_);
v___x_3494_ = v___x_3446_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_methods_3439_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_quotContext_3440_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_currMacroScope_3441_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_currRecDepth_3442_);
lean_ctor_set(v_reuseFailAlloc_3497_, 4, v_maxRecDepth_3443_);
lean_ctor_set(v_reuseFailAlloc_3497_, 5, v_ref_3448_);
v___x_3494_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5));
v___x_3496_ = l_Lean_Macro_throwError___redArg(v___x_3495_, v___x_3494_, v___y_3430_);
lean_dec_ref(v___x_3494_);
return v___x_3496_;
}
}
}
}
v___jp_3499_:
{
lean_object* v_bs_3509_; lean_object* v___x_3510_; 
v_bs_3509_ = l_Lean_Syntax_getArgs(v___y_3505_);
lean_dec(v___y_3505_);
v___x_3510_ = l_Lake_expandBinders(v_bs_3509_, v___y_3507_, v___y_3508_);
lean_dec_ref(v_bs_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v_a_3512_; lean_object* v_ids_3513_; lean_object* v___x_3514_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
v_a_3512_ = lean_ctor_get(v___x_3510_, 1);
lean_inc(v_a_3512_);
lean_dec_ref(v___x_3510_);
v_ids_3513_ = l_Lean_Syntax_getArgs(v___y_3503_);
lean_dec(v___y_3503_);
v___x_3514_ = l_Lake_mkDepArrow(v_a_3511_, v___y_3501_);
if (lean_obj_tag(v___y_3500_) == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3513_);
v___x_3516_ = lean_array_get_size(v___x_3515_);
v___x_3517_ = lean_nat_dec_lt(v___x_3425_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref(v___x_3515_);
lean_dec(v___x_3514_);
lean_dec_ref(v_ids_3513_);
lean_dec(v_a_3511_);
lean_dec(v_val_x3f_3506_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v___x_3518_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6));
v___x_3519_ = l_Lean_Macro_throwError___redArg(v___x_3518_, v___y_3507_, v_a_3512_);
lean_dec_ref(v___y_3507_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; 
v___x_3520_ = lean_array_fget(v___x_3515_, v___x_3425_);
lean_dec_ref(v___x_3515_);
v___y_3430_ = v_a_3512_;
v___y_3431_ = v_ids_3513_;
v___y_3432_ = v___y_3502_;
v___y_3433_ = v___y_3507_;
v___y_3434_ = v___y_3504_;
v___y_3435_ = v_val_x3f_3506_;
v___y_3436_ = v_a_3511_;
v___y_3437_ = v___x_3514_;
v_val_3438_ = v___x_3520_;
goto v___jp_3429_;
}
}
else
{
lean_object* v_val_3521_; 
v_val_3521_ = lean_ctor_get(v___y_3500_, 0);
lean_inc(v_val_3521_);
lean_dec_ref(v___y_3500_);
v___y_3430_ = v_a_3512_;
v___y_3431_ = v_ids_3513_;
v___y_3432_ = v___y_3502_;
v___y_3433_ = v___y_3507_;
v___y_3434_ = v___y_3504_;
v___y_3435_ = v_val_x3f_3506_;
v___y_3436_ = v_a_3511_;
v___y_3437_ = v___x_3514_;
v_val_3438_ = v_val_3521_;
goto v___jp_3429_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v___y_3507_);
lean_dec(v_val_x3f_3506_);
lean_dec(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec(v_mods_3426_);
lean_dec(v_stx_3410_);
v_a_3522_ = lean_ctor_get(v___x_3510_, 0);
v_a_3523_ = lean_ctor_get(v___x_3510_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3510_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_inc(v_a_3522_);
lean_dec(v___x_3510_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3522_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___boxed(lean_object* v_stx_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_stx_3574_, v_a_3575_, v_a_3576_);
lean_dec_ref(v_a_3575_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(lean_object* v_typeName_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3580_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0));
v___x_3581_ = l_Lean_Name_getString_x21(v_typeName_3579_);
v___x_3582_ = lean_string_append(v___x_3580_, v___x_3581_);
lean_dec_ref(v___x_3581_);
v___x_3583_ = lean_box(0);
v___x_3584_ = l_Lean_Name_str___override(v___x_3583_, v___x_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___boxed(lean_object* v_typeName_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_typeName_3585_);
lean_dec(v_typeName_3585_);
return v_res_3586_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6);
v___x_3598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3599_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_3600_ = l_Lean_Syntax_node7(v___x_3599_, v___x_3598_, v___x_3597_, v___x_3597_, v___x_3597_, v___x_3597_, v___x_3597_, v___x_3597_, v___x_3597_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(lean_object* v_stx_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_methods_3606_; lean_object* v_quotContext_3607_; lean_object* v_currMacroScope_3608_; lean_object* v_currRecDepth_3609_; lean_object* v_maxRecDepth_3610_; lean_object* v_ref_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v_id_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v_ref_3642_; lean_object* v___x_3643_; 
v_methods_3606_ = lean_ctor_get(v_a_3604_, 0);
v_quotContext_3607_ = lean_ctor_get(v_a_3604_, 1);
v_currMacroScope_3608_ = lean_ctor_get(v_a_3604_, 2);
v_currRecDepth_3609_ = lean_ctor_get(v_a_3604_, 3);
v_maxRecDepth_3610_ = lean_ctor_get(v_a_3604_, 4);
v_ref_3611_ = lean_ctor_get(v_a_3604_, 5);
v___x_3612_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1));
lean_inc(v_stx_3603_);
v___x_3613_ = l_Lean_Syntax_isOfKind(v_stx_3603_, v___x_3612_);
v_ref_3642_ = l_Lean_replaceRef(v_stx_3603_, v_ref_3611_);
lean_inc(v_maxRecDepth_3610_);
lean_inc(v_currRecDepth_3609_);
lean_inc(v_currMacroScope_3608_);
lean_inc(v_quotContext_3607_);
lean_inc(v_methods_3606_);
v___x_3643_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3643_, 0, v_methods_3606_);
lean_ctor_set(v___x_3643_, 1, v_quotContext_3607_);
lean_ctor_set(v___x_3643_, 2, v_currMacroScope_3608_);
lean_ctor_set(v___x_3643_, 3, v_currRecDepth_3609_);
lean_ctor_set(v___x_3643_, 4, v_maxRecDepth_3610_);
lean_ctor_set(v___x_3643_, 5, v_ref_3642_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec(v_stx_3603_);
v___x_3644_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3645_ = l_Lean_Macro_throwError___redArg(v___x_3644_, v___x_3643_, v_a_3605_);
lean_dec_ref(v___x_3643_);
return v___x_3645_;
}
else
{
lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v_typeId_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___x_3669_; lean_object* v_id_x3f_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
v___x_3709_ = l_Lean_Syntax_getArg(v_stx_3603_, v___x_3669_);
v___x_3710_ = l_Lean_Syntax_isNone(v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3709_);
v___x_3712_ = l_Lean_Syntax_matchesNull(v___x_3709_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec(v___x_3709_);
lean_dec(v_stx_3603_);
v___x_3713_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3714_ = l_Lean_Macro_throwError___redArg(v___x_3713_, v___x_3643_, v_a_3605_);
lean_dec_ref(v___x_3643_);
return v___x_3714_;
}
else
{
lean_object* v_id_x3f_3715_; lean_object* v___x_3716_; 
v_id_x3f_3715_ = l_Lean_Syntax_getArg(v___x_3709_, v___x_3669_);
lean_dec(v___x_3709_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_id_x3f_3715_);
v_id_x3f_3671_ = v___x_3716_;
v___y_3672_ = v___x_3643_;
v___y_3673_ = v_a_3605_;
goto v___jp_3670_;
}
}
else
{
lean_object* v___x_3717_; 
lean_dec(v___x_3709_);
v___x_3717_ = lean_box(0);
v_id_x3f_3671_ = v___x_3717_;
v___y_3672_ = v___x_3643_;
v___y_3673_ = v_a_3605_;
goto v___jp_3670_;
}
v___jp_3646_:
{
lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = l_Lean_TSyntax_getId(v_typeId_3649_);
v___x_3653_ = l_Lean_Name_hasMacroScopes(v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; 
v___x_3654_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v___x_3652_);
lean_dec(v___x_3652_);
v___y_3634_ = v___y_3647_;
v___y_3635_ = v_typeId_3649_;
v___y_3636_ = v___y_3651_;
v___y_3637_ = v___y_3648_;
v___y_3638_ = v___y_3650_;
v___y_3639_ = v___x_3654_;
goto v___jp_3633_;
}
else
{
lean_object* v_view_3655_; lean_object* v_name_3656_; lean_object* v_imported_3657_; lean_object* v_ctx_3658_; lean_object* v_scopes_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3668_; 
v_view_3655_ = l_Lean_extractMacroScopes(v___x_3652_);
v_name_3656_ = lean_ctor_get(v_view_3655_, 0);
v_imported_3657_ = lean_ctor_get(v_view_3655_, 1);
v_ctx_3658_ = lean_ctor_get(v_view_3655_, 2);
v_scopes_3659_ = lean_ctor_get(v_view_3655_, 3);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_view_3655_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3661_ = v_view_3655_;
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_scopes_3659_);
lean_inc(v_ctx_3658_);
lean_inc(v_imported_3657_);
lean_inc(v_name_3656_);
lean_dec(v_view_3655_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3663_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_name_3656_);
lean_dec(v_name_3656_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_imported_3657_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_ctx_3658_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_scopes_3659_);
v___x_3665_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_MacroScopesView_review(v___x_3665_);
v___y_3634_ = v___y_3647_;
v___y_3635_ = v_typeId_3649_;
v___y_3636_ = v___y_3651_;
v___y_3637_ = v___y_3648_;
v___y_3638_ = v___y_3650_;
v___y_3639_ = v___x_3666_;
goto v___jp_3633_;
}
}
}
}
v___jp_3670_:
{
lean_object* v___x_3674_; lean_object* v_id_3675_; 
v___x_3674_ = lean_unsigned_to_nat(1u);
v_id_3675_ = l_Lean_Syntax_getArg(v_stx_3603_, v___x_3674_);
if (lean_obj_tag(v_id_x3f_3671_) == 1)
{
lean_object* v_val_3676_; 
v_val_3676_ = lean_ctor_get(v_id_x3f_3671_, 0);
lean_inc(v_val_3676_);
lean_dec_ref(v_id_x3f_3671_);
v___y_3615_ = v_id_3675_;
v___y_3616_ = v___x_3674_;
v_id_3617_ = v_val_3676_;
v___y_3618_ = v___y_3672_;
v___y_3619_ = v___y_3673_;
goto v___jp_3614_;
}
else
{
lean_object* v___x_3677_; uint8_t v___x_3678_; 
lean_dec(v_id_x3f_3671_);
v___x_3677_ = ((lean_object*)(l_Lake_configField___closed__13));
lean_inc(v_id_3675_);
v___x_3678_ = l_Lean_Syntax_isOfKind(v_id_3675_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
lean_inc(v_id_3675_);
v___x_3680_ = l_Lean_Syntax_isOfKind(v_id_3675_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3682_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3675_, v___x_3681_, v___y_3672_, v___y_3673_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_a_3684_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
v_a_3684_ = lean_ctor_get(v___x_3682_, 1);
lean_inc(v_a_3684_);
lean_dec_ref(v___x_3682_);
v___y_3647_ = v_id_3675_;
v___y_3648_ = v___x_3674_;
v_typeId_3649_ = v_a_3683_;
v___y_3650_ = v___y_3672_;
v___y_3651_ = v_a_3684_;
goto v___jp_3646_;
}
else
{
lean_object* v_a_3685_; lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_id_3675_);
lean_dec_ref(v___y_3672_);
lean_dec(v_stx_3603_);
v_a_3685_ = lean_ctor_get(v___x_3682_, 0);
v_a_3686_ = lean_ctor_get(v___x_3682_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3682_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_inc(v_a_3685_);
lean_dec(v___x_3682_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3685_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_id_3694_; uint8_t v___x_3695_; 
v_id_3694_ = l_Lean_Syntax_getArg(v_id_3675_, v___x_3669_);
lean_inc(v_id_3694_);
v___x_3695_ = l_Lean_Syntax_isOfKind(v_id_3694_, v___x_3677_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_id_3694_);
v___x_3696_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3697_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3675_, v___x_3696_, v___y_3672_, v___y_3673_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v_a_3699_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
v_a_3699_ = lean_ctor_get(v___x_3697_, 1);
lean_inc(v_a_3699_);
lean_dec_ref(v___x_3697_);
v___y_3647_ = v_id_3675_;
v___y_3648_ = v___x_3674_;
v_typeId_3649_ = v_a_3698_;
v___y_3650_ = v___y_3672_;
v___y_3651_ = v_a_3699_;
goto v___jp_3646_;
}
else
{
lean_object* v_a_3700_; lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_id_3675_);
lean_dec_ref(v___y_3672_);
lean_dec(v_stx_3603_);
v_a_3700_ = lean_ctor_get(v___x_3697_, 0);
v_a_3701_ = lean_ctor_get(v___x_3697_, 1);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3697_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_inc(v_a_3700_);
lean_dec(v___x_3697_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3700_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
v___y_3647_ = v_id_3675_;
v___y_3648_ = v___x_3674_;
v_typeId_3649_ = v_id_3694_;
v___y_3650_ = v___y_3672_;
v___y_3651_ = v___y_3673_;
goto v___jp_3646_;
}
}
}
else
{
lean_inc(v_id_3675_);
v___y_3647_ = v_id_3675_;
v___y_3648_ = v___x_3674_;
v_typeId_3649_ = v_id_3675_;
v___y_3650_ = v___y_3672_;
v___y_3651_ = v___y_3673_;
goto v___jp_3646_;
}
}
}
}
v___jp_3614_:
{
lean_object* v_ref_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_ref_3620_ = lean_ctor_get(v___y_3618_, 5);
lean_inc(v_ref_3620_);
lean_dec_ref(v___y_3618_);
v___x_3621_ = 0;
v___x_3622_ = l_Lean_SourceInfo_fromRef(v_ref_3620_, v___x_3621_);
lean_dec(v_ref_3620_);
v___x_3623_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3));
v___x_3624_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4));
lean_inc(v___x_3622_);
v___x_3625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3622_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = l_Lean_Syntax_node1(v___x_3622_, v___x_3623_, v___x_3625_);
v___x_3627_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5);
v___x_3628_ = lean_mk_empty_array_with_capacity(v___y_3616_);
lean_inc(v_id_3617_);
v___x_3629_ = lean_array_push(v___x_3628_, v_id_3617_);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3631_, 0, v_stx_3603_);
lean_ctor_set(v___x_3631_, 1, v___x_3627_);
lean_ctor_set(v___x_3631_, 2, v_id_3617_);
lean_ctor_set(v___x_3631_, 3, v___x_3629_);
lean_ctor_set(v___x_3631_, 4, v___y_3615_);
lean_ctor_set(v___x_3631_, 5, v___x_3626_);
lean_ctor_set(v___x_3631_, 6, v___x_3630_);
lean_ctor_set_uint8(v___x_3631_, sizeof(void*)*7, v___x_3613_);
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
lean_ctor_set(v___x_3632_, 1, v___y_3619_);
return v___x_3632_;
}
v___jp_3633_:
{
uint8_t v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = 0;
v___x_3641_ = l_Lean_mkIdentFrom(v___y_3635_, v___y_3639_, v___x_3640_);
lean_dec(v___y_3635_);
v___y_3615_ = v___y_3634_;
v___y_3616_ = v___y_3637_;
v_id_3617_ = v___x_3641_;
v___y_3618_ = v___y_3638_;
v___y_3619_ = v___y_3636_;
goto v___jp_3614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___boxed(lean_object* v_stx_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v_stx_3718_, v_a_3719_, v_a_3720_);
lean_dec_ref(v_a_3719_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__0(lean_object* v_x_3722_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___x_3724_ = lean_array_push(v___x_3723_, v_x_3722_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__1(lean_object* v_00___3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(size_t v_sz_3727_, size_t v_i_3728_, lean_object* v_bs_3729_){
_start:
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_usize_dec_lt(v_i_3728_, v_sz_3727_);
if (v___x_3730_ == 0)
{
return v_bs_3729_;
}
else
{
lean_object* v_v_3731_; lean_object* v___x_3732_; lean_object* v_bs_x27_3733_; size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v_v_3731_ = lean_array_uget(v_bs_3729_, v_i_3728_);
v___x_3732_ = lean_unsigned_to_nat(0u);
v_bs_x27_3733_ = lean_array_uset(v_bs_3729_, v_i_3728_, v___x_3732_);
v___x_3734_ = ((size_t)1ULL);
v___x_3735_ = lean_usize_add(v_i_3728_, v___x_3734_);
v___x_3736_ = lean_array_uset(v_bs_x27_3733_, v_i_3728_, v_v_3731_);
v_i_3728_ = v___x_3735_;
v_bs_3729_ = v___x_3736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3___boxed(lean_object* v_sz_3738_, lean_object* v_i_3739_, lean_object* v_bs_3740_){
_start:
{
size_t v_sz_boxed_3741_; size_t v_i_boxed_3742_; lean_object* v_res_3743_; 
v_sz_boxed_3741_ = lean_unbox_usize(v_sz_3738_);
lean_dec(v_sz_3738_);
v_i_boxed_3742_ = lean_unbox_usize(v_i_3739_);
lean_dec(v_i_3739_);
v_res_3743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_boxed_3741_, v_i_boxed_3742_, v_bs_3740_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(size_t v_sz_3744_, size_t v_i_3745_, lean_object* v_bs_3746_){
_start:
{
uint8_t v___x_3747_; 
v___x_3747_ = lean_usize_dec_lt(v_i_3745_, v_sz_3744_);
if (v___x_3747_ == 0)
{
return v_bs_3746_;
}
else
{
lean_object* v_v_3748_; lean_object* v___x_3749_; lean_object* v_bs_x27_3750_; size_t v___x_3751_; size_t v___x_3752_; lean_object* v___x_3753_; 
v_v_3748_ = lean_array_uget(v_bs_3746_, v_i_3745_);
v___x_3749_ = lean_unsigned_to_nat(0u);
v_bs_x27_3750_ = lean_array_uset(v_bs_3746_, v_i_3745_, v___x_3749_);
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3745_, v___x_3751_);
v___x_3753_ = lean_array_uset(v_bs_x27_3750_, v_i_3745_, v_v_3748_);
v_i_3745_ = v___x_3752_;
v_bs_3746_ = v___x_3753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6___boxed(lean_object* v_sz_3755_, lean_object* v_i_3756_, lean_object* v_bs_3757_){
_start:
{
size_t v_sz_boxed_3758_; size_t v_i_boxed_3759_; lean_object* v_res_3760_; 
v_sz_boxed_3758_ = lean_unbox_usize(v_sz_3755_);
lean_dec(v_sz_3755_);
v_i_boxed_3759_ = lean_unbox_usize(v_i_3756_);
lean_dec(v_i_3756_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_boxed_3758_, v_i_boxed_3759_, v_bs_3757_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(size_t v_sz_3761_, size_t v_i_3762_, lean_object* v_bs_3763_){
_start:
{
uint8_t v___x_3764_; 
v___x_3764_ = lean_usize_dec_lt(v_i_3762_, v_sz_3761_);
if (v___x_3764_ == 0)
{
return v_bs_3763_;
}
else
{
lean_object* v_v_3765_; lean_object* v___x_3766_; lean_object* v_bs_x27_3767_; size_t v___x_3768_; size_t v___x_3769_; lean_object* v___x_3770_; 
v_v_3765_ = lean_array_uget(v_bs_3763_, v_i_3762_);
v___x_3766_ = lean_unsigned_to_nat(0u);
v_bs_x27_3767_ = lean_array_uset(v_bs_3763_, v_i_3762_, v___x_3766_);
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = lean_usize_add(v_i_3762_, v___x_3768_);
v___x_3770_ = lean_array_uset(v_bs_x27_3767_, v_i_3762_, v_v_3765_);
v_i_3762_ = v___x_3769_;
v_bs_3763_ = v___x_3770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5___boxed(lean_object* v_sz_3772_, lean_object* v_i_3773_, lean_object* v_bs_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3772_);
lean_dec(v_sz_3772_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3773_);
lean_dec(v_i_3773_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_boxed_3775_, v_i_boxed_3776_, v_bs_3774_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(lean_object* v_as_3778_, size_t v_i_3779_, size_t v_stop_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_eq(v_i_3779_, v_stop_3780_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_array_uget_borrowed(v_as_3778_, v_i_3779_);
lean_inc(v___x_3785_);
v___x_3786_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v___x_3785_, v___y_3782_, v___y_3783_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v_a_3788_; lean_object* v___x_3789_; size_t v___x_3790_; size_t v___x_3791_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
v_a_3788_ = lean_ctor_get(v___x_3786_, 1);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3786_);
v___x_3789_ = lean_array_push(v_b_3781_, v_a_3787_);
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3779_, v___x_3790_);
v_i_3779_ = v___x_3791_;
v_b_3781_ = v___x_3789_;
v___y_3783_ = v_a_3788_;
goto _start;
}
else
{
lean_object* v_a_3793_; lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_b_3781_);
v_a_3793_ = lean_ctor_get(v___x_3786_, 0);
v_a_3794_ = lean_ctor_get(v___x_3786_, 1);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3786_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_inc(v_a_3793_);
lean_dec(v___x_3786_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3793_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v_b_3781_);
lean_ctor_set(v___x_3802_, 1, v___y_3783_);
return v___x_3802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8___boxed(lean_object* v_as_3803_, lean_object* v_i_3804_, lean_object* v_stop_3805_, lean_object* v_b_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_i_boxed_3809_; size_t v_stop_boxed_3810_; lean_object* v_res_3811_; 
v_i_boxed_3809_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_stop_boxed_3810_ = lean_unbox_usize(v_stop_3805_);
lean_dec(v_stop_3805_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v_as_3803_, v_i_boxed_3809_, v_stop_boxed_3810_, v_b_3806_, v___y_3807_, v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec_ref(v_as_3803_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(lean_object* v_as_3812_, size_t v_i_3813_, size_t v_stop_3814_, lean_object* v_b_3815_){
_start:
{
lean_object* v___y_3817_; uint8_t v___x_3821_; 
v___x_3821_ = lean_usize_dec_eq(v_i_3813_, v_stop_3814_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; lean_object* v_decl_x3f_3823_; 
v___x_3822_ = lean_array_uget_borrowed(v_as_3812_, v_i_3813_);
v_decl_x3f_3823_ = lean_ctor_get(v___x_3822_, 6);
if (lean_obj_tag(v_decl_x3f_3823_) == 0)
{
v___y_3817_ = v_b_3815_;
goto v___jp_3816_;
}
else
{
lean_object* v_val_3824_; lean_object* v___x_3825_; 
v_val_3824_ = lean_ctor_get(v_decl_x3f_3823_, 0);
lean_inc(v_val_3824_);
v___x_3825_ = lean_array_push(v_b_3815_, v_val_3824_);
v___y_3817_ = v___x_3825_;
goto v___jp_3816_;
}
}
else
{
return v_b_3815_;
}
v___jp_3816_:
{
size_t v___x_3818_; size_t v___x_3819_; 
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_add(v_i_3813_, v___x_3818_);
v_i_3813_ = v___x_3819_;
v_b_3815_ = v___y_3817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2___boxed(lean_object* v_as_3826_, lean_object* v_i_3827_, lean_object* v_stop_3828_, lean_object* v_b_3829_){
_start:
{
size_t v_i_boxed_3830_; size_t v_stop_boxed_3831_; lean_object* v_res_3832_; 
v_i_boxed_3830_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_stop_boxed_3831_ = lean_unbox_usize(v_stop_3828_);
lean_dec(v_stop_3828_);
v_res_3832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3826_, v_i_boxed_3830_, v_stop_boxed_3831_, v_b_3829_);
lean_dec_ref(v_as_3826_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(lean_object* v_as_3833_, lean_object* v_start_3834_, lean_object* v_stop_3835_){
_start:
{
lean_object* v___x_3836_; uint8_t v___x_3837_; 
v___x_3836_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___x_3837_ = lean_nat_dec_lt(v_start_3834_, v_stop_3835_);
if (v___x_3837_ == 0)
{
return v___x_3836_;
}
else
{
lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = lean_array_get_size(v_as_3833_);
v___x_3839_ = lean_nat_dec_le(v_stop_3835_, v___x_3838_);
if (v___x_3839_ == 0)
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_nat_dec_lt(v_start_3834_, v___x_3838_);
if (v___x_3840_ == 0)
{
return v___x_3836_;
}
else
{
size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_usize_of_nat(v_start_3834_);
v___x_3842_ = lean_usize_of_nat(v___x_3838_);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3833_, v___x_3841_, v___x_3842_, v___x_3836_);
return v___x_3843_;
}
}
else
{
size_t v___x_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_usize_of_nat(v_start_3834_);
v___x_3845_ = lean_usize_of_nat(v_stop_3835_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3833_, v___x_3844_, v___x_3845_, v___x_3836_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2___boxed(lean_object* v_as_3847_, lean_object* v_start_3848_, lean_object* v_stop_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_as_3847_, v_start_3848_, v_stop_3849_);
lean_dec(v_stop_3849_);
lean_dec(v_start_3848_);
lean_dec_ref(v_as_3847_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(size_t v_sz_3851_, size_t v_i_3852_, lean_object* v_bs_3853_){
_start:
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_usize_dec_lt(v_i_3852_, v_sz_3851_);
if (v___x_3854_ == 0)
{
return v_bs_3853_;
}
else
{
lean_object* v_v_3855_; lean_object* v___x_3856_; lean_object* v_bs_x27_3857_; size_t v___x_3858_; size_t v___x_3859_; lean_object* v___x_3860_; 
v_v_3855_ = lean_array_uget(v_bs_3853_, v_i_3852_);
v___x_3856_ = lean_unsigned_to_nat(0u);
v_bs_x27_3857_ = lean_array_uset(v_bs_3853_, v_i_3852_, v___x_3856_);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3852_, v___x_3858_);
v___x_3860_ = lean_array_uset(v_bs_x27_3857_, v_i_3852_, v_v_3855_);
v_i_3852_ = v___x_3859_;
v_bs_3853_ = v___x_3860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7___boxed(lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_bs_3864_){
_start:
{
size_t v_sz_boxed_3865_; size_t v_i_boxed_3866_; lean_object* v_res_3867_; 
v_sz_boxed_3865_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3866_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_boxed_3865_, v_i_boxed_3866_, v_bs_3864_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(size_t v_sz_3868_, size_t v_i_3869_, lean_object* v_bs_3870_){
_start:
{
uint8_t v___x_3871_; 
v___x_3871_ = lean_usize_dec_lt(v_i_3869_, v_sz_3868_);
if (v___x_3871_ == 0)
{
return v_bs_3870_;
}
else
{
lean_object* v_v_3872_; lean_object* v___x_3873_; lean_object* v_bs_x27_3874_; lean_object* v___x_3875_; size_t v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
v_v_3872_ = lean_array_uget(v_bs_3870_, v_i_3869_);
v___x_3873_ = lean_unsigned_to_nat(0u);
v_bs_x27_3874_ = lean_array_uset(v_bs_3870_, v_i_3869_, v___x_3873_);
v___x_3875_ = l_Lake_BinderSyntaxView_mkArgument(v_v_3872_);
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_add(v_i_3869_, v___x_3876_);
v___x_3878_ = lean_array_uset(v_bs_x27_3874_, v_i_3869_, v___x_3875_);
v_i_3869_ = v___x_3877_;
v_bs_3870_ = v___x_3878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0___boxed(lean_object* v_sz_3880_, lean_object* v_i_3881_, lean_object* v_bs_3882_){
_start:
{
size_t v_sz_boxed_3883_; size_t v_i_boxed_3884_; lean_object* v_res_3885_; 
v_sz_boxed_3883_ = lean_unbox_usize(v_sz_3880_);
lean_dec(v_sz_3880_);
v_i_boxed_3884_ = lean_unbox_usize(v_i_3881_);
lean_dec(v_i_3881_);
v_res_3885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_boxed_3883_, v_i_boxed_3884_, v_bs_3882_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(size_t v_sz_3886_, size_t v_i_3887_, lean_object* v_bs_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_usize_dec_lt(v_i_3887_, v_sz_3886_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v_bs_3888_);
lean_ctor_set(v___x_3892_, 1, v___y_3890_);
return v___x_3892_;
}
else
{
lean_object* v_v_3893_; lean_object* v___x_3894_; 
v_v_3893_ = lean_array_uget_borrowed(v_bs_3888_, v_i_3887_);
lean_inc(v_v_3893_);
v___x_3894_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_v_3893_, v___y_3889_, v___y_3890_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v_bs_x27_3898_; size_t v___x_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
v_a_3896_ = lean_ctor_get(v___x_3894_, 1);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3894_);
v___x_3897_ = lean_unsigned_to_nat(0u);
v_bs_x27_3898_ = lean_array_uset(v_bs_3888_, v_i_3887_, v___x_3897_);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_add(v_i_3887_, v___x_3899_);
v___x_3901_ = lean_array_uset(v_bs_x27_3898_, v_i_3887_, v_a_3895_);
v_i_3887_ = v___x_3900_;
v_bs_3888_ = v___x_3901_;
v___y_3890_ = v_a_3896_;
goto _start;
}
else
{
lean_object* v_a_3903_; lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec_ref(v_bs_3888_);
v_a_3903_ = lean_ctor_get(v___x_3894_, 0);
v_a_3904_ = lean_ctor_get(v___x_3894_, 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3894_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_inc(v_a_3903_);
lean_dec(v___x_3894_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3903_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1___boxed(lean_object* v_sz_3912_, lean_object* v_i_3913_, lean_object* v_bs_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
size_t v_sz_boxed_3917_; size_t v_i_boxed_3918_; lean_object* v_res_3919_; 
v_sz_boxed_3917_ = lean_unbox_usize(v_sz_3912_);
lean_dec(v_sz_3912_);
v_i_boxed_3918_ = lean_unbox_usize(v_i_3913_);
lean_dec(v_i_3913_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_boxed_3917_, v_i_boxed_3918_, v_bs_3914_, v___y_3915_, v___y_3916_);
lean_dec_ref(v___y_3915_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(size_t v_sz_3920_, size_t v_i_3921_, lean_object* v_bs_3922_){
_start:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_usize_dec_lt(v_i_3921_, v_sz_3920_);
if (v___x_3923_ == 0)
{
return v_bs_3922_;
}
else
{
lean_object* v_v_3924_; lean_object* v___x_3925_; lean_object* v_bs_x27_3926_; size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; 
v_v_3924_ = lean_array_uget(v_bs_3922_, v_i_3921_);
v___x_3925_ = lean_unsigned_to_nat(0u);
v_bs_x27_3926_ = lean_array_uset(v_bs_3922_, v_i_3921_, v___x_3925_);
v___x_3927_ = ((size_t)1ULL);
v___x_3928_ = lean_usize_add(v_i_3921_, v___x_3927_);
v___x_3929_ = lean_array_uset(v_bs_x27_3926_, v_i_3921_, v_v_3924_);
v_i_3921_ = v___x_3928_;
v_bs_3922_ = v___x_3929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4___boxed(lean_object* v_sz_3931_, lean_object* v_i_3932_, lean_object* v_bs_3933_){
_start:
{
size_t v_sz_boxed_3934_; size_t v_i_boxed_3935_; lean_object* v_res_3936_; 
v_sz_boxed_3934_ = lean_unbox_usize(v_sz_3931_);
lean_dec(v_sz_3931_);
v_i_boxed_3935_ = lean_unbox_usize(v_i_3932_);
lean_dec(v_i_3932_);
v_res_3936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_boxed_3934_, v_i_boxed_3935_, v_bs_3933_);
return v_res_3936_;
}
}
static lean_object* _init_l_Lake_expandConfigDecl___closed__3(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_box(0);
v___x_3945_ = l_Lake_expandConfigDecl___lam__1(v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl(lean_object* v_stx_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lake_configDecl___closed__1));
lean_inc(v_stx_3958_);
v___x_3962_ = l_Lean_Syntax_isOfKind(v_stx_3958_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec(v_stx_3958_);
v___x_3963_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3964_ = l_Lean_Macro_throwError___redArg(v___x_3963_, v_a_3959_, v_a_3960_);
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v___x_3966_);
v___x_3968_ = l_Lean_Syntax_isOfKind(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_3969_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3970_ = l_Lean_Macro_throwError___redArg(v___x_3969_, v_a_3959_, v_a_3960_);
return v___x_3970_;
}
else
{
lean_object* v___x_3971_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v_tk_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; size_t v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; size_t v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; size_t v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; size_t v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; size_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; size_t v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v_a_4174_; lean_object* v_a_4175_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; size_t v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; size_t v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; size_t v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v_ctor_x3f_4281_; lean_object* v_fs_x3f_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v_ctor_x3f_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4328_; lean_object* v_ps_x3f_4329_; lean_object* v_xty_x3f_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v_xty_x3f_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v_ty_x3f_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_3971_ = lean_unsigned_to_nat(1u);
v_tk_4007_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_3971_);
v___x_4008_ = lean_unsigned_to_nat(2u);
v___x_4009_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4008_);
v___x_4275_ = lean_unsigned_to_nat(3u);
v___x_4276_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4275_);
v___x_4387_ = lean_unsigned_to_nat(4u);
v___x_4388_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4387_);
v___x_4389_ = l_Lean_Syntax_isNone(v___x_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
lean_inc(v___x_4388_);
v___x_4390_ = l_Lean_Syntax_matchesNull(v___x_4388_, v___x_3971_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
lean_dec(v___x_4388_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4391_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4392_ = l_Lean_Macro_throwError___redArg(v___x_4391_, v_a_3959_, v_a_3960_);
return v___x_4392_;
}
else
{
lean_object* v_ty_x3f_4393_; lean_object* v___x_4394_; 
v_ty_x3f_4393_ = l_Lean_Syntax_getArg(v___x_4388_, v___x_3965_);
lean_dec(v___x_4388_);
v___x_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4394_, 0, v_ty_x3f_4393_);
v_ty_x3f_4363_ = v___x_4394_;
v___y_4364_ = v_a_3959_;
v___y_4365_ = v_a_3960_;
goto v___jp_4362_;
}
}
else
{
lean_object* v___x_4395_; 
lean_dec(v___x_4388_);
v___x_4395_ = lean_box(0);
v_ty_x3f_4363_ = v___x_4395_;
v___y_4364_ = v_a_3959_;
v___y_4365_ = v_a_3960_;
goto v___jp_4362_;
}
v___jp_3972_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_array_get_size(v___y_3979_);
lean_dec_ref(v___y_3979_);
v___x_3983_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v___y_3981_, v___y_3980_, v___x_3982_, v___y_3976_, v___y_3978_, v___y_3973_, v___y_3974_);
lean_dec_ref(v___y_3973_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3997_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_a_3985_ = lean_ctor_get(v___x_3983_, 1);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3987_ = v___x_3983_;
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3989_ = lean_mk_empty_array_with_capacity(v___x_3971_);
v___x_3990_ = lean_array_push(v___x_3989_, v___y_3975_);
v___x_3991_ = l_Array_append___redArg(v___x_3990_, v_a_3984_);
lean_dec(v_a_3984_);
v___x_3992_ = lean_box(2);
lean_inc(v___y_3977_);
v___x_3993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
lean_ctor_set(v___x_3993_, 1, v___y_3977_);
lean_ctor_set(v___x_3993_, 2, v___x_3991_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3993_);
v___x_3995_ = v___x_3987_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_a_3985_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec(v___y_3975_);
v_a_3998_ = lean_ctor_get(v___x_3983_, 0);
v_a_3999_ = lean_ctor_get(v___x_3983_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3983_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_inc(v_a_3998_);
lean_dec(v___x_3983_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3998_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
v___jp_4010_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; size_t v_sz_4033_; lean_object* v___x_4034_; size_t v_sz_4035_; lean_object* v___x_4036_; size_t v_sz_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_inc_ref(v___y_4023_);
v___x_4030_ = l_Array_append___redArg(v___y_4023_, v___y_4029_);
lean_dec_ref(v___y_4029_);
lean_inc_n(v___y_4024_, 3);
lean_inc_n(v___y_4011_, 5);
v___x_4031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4031_, 0, v___y_4011_);
lean_ctor_set(v___x_4031_, 1, v___y_4024_);
lean_ctor_set(v___x_4031_, 2, v___x_4030_);
v___x_4032_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__2));
v_sz_4033_ = lean_array_size(v___y_4021_);
v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_4033_, v___y_4027_, v___y_4021_);
v_sz_4035_ = lean_array_size(v___x_4034_);
v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_4035_, v___y_4027_, v___x_4034_);
v_sz_4037_ = lean_array_size(v___x_4036_);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_4037_, v___y_4027_, v___x_4036_);
v___x_4039_ = l_Array_append___redArg(v___y_4023_, v___x_4038_);
lean_dec_ref(v___x_4038_);
v___x_4040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4011_);
lean_ctor_set(v___x_4040_, 1, v___y_4024_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
v___x_4041_ = l_Lean_Syntax_node1(v___y_4011_, v___x_4032_, v___x_4040_);
v___x_4042_ = l_Lean_Syntax_node3(v___y_4011_, v___y_4024_, v___y_4017_, v___x_4031_, v___x_4041_);
lean_inc(v___y_4012_);
v___x_4043_ = l_Lean_Syntax_node6(v___y_4011_, v___y_4012_, v___y_4019_, v___x_4009_, v___y_4025_, v___y_4028_, v___x_4042_, v___y_4013_);
lean_inc(v___x_3966_);
lean_inc(v___y_4016_);
v___x_4044_ = l_Lean_Syntax_node2(v___y_4011_, v___y_4016_, v___x_3966_, v___x_4043_);
v___x_4045_ = l_Lean_Syntax_getArg(v___x_3966_, v___x_4008_);
lean_dec(v___x_3966_);
v___x_4046_ = l_Lean_Syntax_getOptional_x3f(v___x_4045_);
lean_dec(v___x_4045_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_box(0);
v___y_3973_ = v___y_4014_;
v___y_3974_ = v___y_4015_;
v___y_3975_ = v___x_4044_;
v___y_3976_ = v___y_4022_;
v___y_3977_ = v___y_4024_;
v___y_3978_ = v___y_4026_;
v___y_3979_ = v___y_4018_;
v___y_3980_ = v___y_4020_;
v___y_3981_ = v___x_4047_;
goto v___jp_3972_;
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_val_4048_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4046_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_val_4048_);
lean_dec(v___x_4046_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_val_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
v___y_3973_ = v___y_4014_;
v___y_3974_ = v___y_4015_;
v___y_3975_ = v___x_4044_;
v___y_3976_ = v___y_4022_;
v___y_3977_ = v___y_4024_;
v___y_3978_ = v___y_4026_;
v___y_3979_ = v___y_4018_;
v___y_3980_ = v___y_4020_;
v___y_3981_ = v___x_4053_;
goto v___jp_3972_;
}
}
}
}
v___jp_4056_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_4011_ = v___y_4057_;
v___y_4012_ = v___y_4058_;
v___y_4013_ = v___y_4059_;
v___y_4014_ = v___y_4060_;
v___y_4015_ = v___y_4061_;
v___y_4016_ = v___y_4062_;
v___y_4017_ = v___y_4063_;
v___y_4018_ = v___y_4064_;
v___y_4019_ = v___y_4065_;
v___y_4020_ = v___y_4066_;
v___y_4021_ = v___y_4067_;
v___y_4022_ = v___y_4068_;
v___y_4023_ = v___y_4069_;
v___y_4024_ = v___y_4071_;
v___y_4025_ = v___y_4070_;
v___y_4026_ = v___y_4072_;
v___y_4027_ = v___y_4073_;
v___y_4028_ = v___y_4074_;
v___y_4029_ = v___x_4075_;
goto v___jp_4010_;
}
v___jp_4076_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_inc_ref(v___y_4091_);
v___x_4098_ = l_Array_append___redArg(v___y_4091_, v___y_4097_);
lean_dec_ref(v___y_4097_);
lean_inc_n(v___y_4093_, 2);
lean_inc_n(v___y_4077_, 4);
v___x_4099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4077_);
lean_ctor_set(v___x_4099_, 1, v___y_4093_);
lean_ctor_set(v___x_4099_, 2, v___x_4098_);
lean_inc(v___y_4084_);
v___x_4100_ = l_Lean_Syntax_node3(v___y_4077_, v___y_4084_, v___y_4078_, v___y_4096_, v___x_4099_);
v___x_4101_ = l_Lean_Syntax_node1(v___y_4077_, v___y_4093_, v___x_4100_);
v___x_4102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_4103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___y_4077_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
if (lean_obj_tag(v___y_4085_) == 0)
{
v___y_4057_ = v___y_4077_;
v___y_4058_ = v___y_4079_;
v___y_4059_ = v___y_4080_;
v___y_4060_ = v___y_4081_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v___y_4083_;
v___y_4063_ = v___x_4103_;
v___y_4064_ = v___y_4086_;
v___y_4065_ = v___y_4087_;
v___y_4066_ = v___y_4088_;
v___y_4067_ = v___y_4089_;
v___y_4068_ = v___y_4090_;
v___y_4069_ = v___y_4091_;
v___y_4070_ = v___y_4092_;
v___y_4071_ = v___y_4093_;
v___y_4072_ = v___y_4094_;
v___y_4073_ = v___y_4095_;
v___y_4074_ = v___x_4101_;
goto v___jp_4056_;
}
else
{
lean_object* v_val_4104_; 
v_val_4104_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_val_4104_);
lean_dec_ref(v___y_4085_);
if (lean_obj_tag(v_val_4104_) == 0)
{
v___y_4057_ = v___y_4077_;
v___y_4058_ = v___y_4079_;
v___y_4059_ = v___y_4080_;
v___y_4060_ = v___y_4081_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v___y_4083_;
v___y_4063_ = v___x_4103_;
v___y_4064_ = v___y_4086_;
v___y_4065_ = v___y_4087_;
v___y_4066_ = v___y_4088_;
v___y_4067_ = v___y_4089_;
v___y_4068_ = v___y_4090_;
v___y_4069_ = v___y_4091_;
v___y_4070_ = v___y_4092_;
v___y_4071_ = v___y_4093_;
v___y_4072_ = v___y_4094_;
v___y_4073_ = v___y_4095_;
v___y_4074_ = v___x_4101_;
goto v___jp_4056_;
}
else
{
lean_object* v_val_4105_; lean_object* v___x_4106_; 
v_val_4105_ = lean_ctor_get(v_val_4104_, 0);
lean_inc(v_val_4105_);
lean_dec_ref(v_val_4104_);
v___x_4106_ = l_Lake_expandConfigDecl___lam__0(v_val_4105_);
v___y_4011_ = v___y_4077_;
v___y_4012_ = v___y_4079_;
v___y_4013_ = v___y_4080_;
v___y_4014_ = v___y_4081_;
v___y_4015_ = v___y_4082_;
v___y_4016_ = v___y_4083_;
v___y_4017_ = v___x_4103_;
v___y_4018_ = v___y_4086_;
v___y_4019_ = v___y_4087_;
v___y_4020_ = v___y_4088_;
v___y_4021_ = v___y_4089_;
v___y_4022_ = v___y_4090_;
v___y_4023_ = v___y_4091_;
v___y_4024_ = v___y_4093_;
v___y_4025_ = v___y_4092_;
v___y_4026_ = v___y_4094_;
v___y_4027_ = v___y_4095_;
v___y_4028_ = v___x_4101_;
v___y_4029_ = v___x_4106_;
goto v___jp_4010_;
}
}
}
v___jp_4107_:
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_4077_ = v___y_4108_;
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4110_;
v___y_4080_ = v___y_4111_;
v___y_4081_ = v___y_4112_;
v___y_4082_ = v___y_4113_;
v___y_4083_ = v___y_4114_;
v___y_4084_ = v___y_4115_;
v___y_4085_ = v___y_4116_;
v___y_4086_ = v___y_4117_;
v___y_4087_ = v___y_4118_;
v___y_4088_ = v___y_4119_;
v___y_4089_ = v___y_4120_;
v___y_4090_ = v___y_4122_;
v___y_4091_ = v___y_4121_;
v___y_4092_ = v___y_4124_;
v___y_4093_ = v___y_4123_;
v___y_4094_ = v___y_4125_;
v___y_4095_ = v___y_4126_;
v___y_4096_ = v___y_4127_;
v___y_4097_ = v___x_4128_;
goto v___jp_4076_;
}
v___jp_4129_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_inc_ref_n(v___y_4143_, 2);
v___x_4151_ = l_Array_append___redArg(v___y_4143_, v___y_4150_);
lean_dec_ref(v___y_4150_);
lean_inc_n(v___y_4144_, 2);
lean_inc_n(v___y_4130_, 4);
v___x_4152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4152_, 0, v___y_4130_);
lean_ctor_set(v___x_4152_, 1, v___y_4144_);
lean_ctor_set(v___x_4152_, 2, v___x_4151_);
lean_inc(v___y_4148_);
v___x_4153_ = l_Lean_Syntax_node2(v___y_4130_, v___y_4148_, v___y_4145_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l_Lake_configDecl___closed__32));
v___x_4155_ = ((lean_object*)(l_Lake_configDecl___closed__33));
v___x_4156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4130_);
lean_ctor_set(v___x_4156_, 1, v___x_4154_);
v___x_4157_ = l_Array_append___redArg(v___y_4143_, v___y_4141_);
lean_dec_ref(v___y_4141_);
v___x_4158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4158_, 0, v___y_4130_);
lean_ctor_set(v___x_4158_, 1, v___y_4144_);
lean_ctor_set(v___x_4158_, 2, v___x_4157_);
if (lean_obj_tag(v___y_4149_) == 0)
{
v___y_4108_ = v___y_4130_;
v___y_4109_ = v___x_4156_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4132_;
v___y_4112_ = v___y_4133_;
v___y_4113_ = v___y_4134_;
v___y_4114_ = v___y_4135_;
v___y_4115_ = v___x_4155_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___y_4138_;
v___y_4119_ = v___y_4139_;
v___y_4120_ = v___y_4140_;
v___y_4121_ = v___y_4143_;
v___y_4122_ = v___y_4142_;
v___y_4123_ = v___y_4144_;
v___y_4124_ = v___x_4153_;
v___y_4125_ = v___y_4146_;
v___y_4126_ = v___y_4147_;
v___y_4127_ = v___x_4158_;
goto v___jp_4107_;
}
else
{
lean_object* v_val_4159_; 
v_val_4159_ = lean_ctor_get(v___y_4149_, 0);
lean_inc(v_val_4159_);
lean_dec_ref(v___y_4149_);
if (lean_obj_tag(v_val_4159_) == 0)
{
v___y_4108_ = v___y_4130_;
v___y_4109_ = v___x_4156_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4132_;
v___y_4112_ = v___y_4133_;
v___y_4113_ = v___y_4134_;
v___y_4114_ = v___y_4135_;
v___y_4115_ = v___x_4155_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___y_4138_;
v___y_4119_ = v___y_4139_;
v___y_4120_ = v___y_4140_;
v___y_4121_ = v___y_4143_;
v___y_4122_ = v___y_4142_;
v___y_4123_ = v___y_4144_;
v___y_4124_ = v___x_4153_;
v___y_4125_ = v___y_4146_;
v___y_4126_ = v___y_4147_;
v___y_4127_ = v___x_4158_;
goto v___jp_4107_;
}
else
{
lean_object* v_val_4160_; lean_object* v___x_4161_; 
v_val_4160_ = lean_ctor_get(v_val_4159_, 0);
lean_inc(v_val_4160_);
lean_dec_ref(v_val_4159_);
v___x_4161_ = l_Lake_expandConfigDecl___lam__0(v_val_4160_);
v___y_4077_ = v___y_4130_;
v___y_4078_ = v___x_4156_;
v___y_4079_ = v___y_4131_;
v___y_4080_ = v___y_4132_;
v___y_4081_ = v___y_4133_;
v___y_4082_ = v___y_4134_;
v___y_4083_ = v___y_4135_;
v___y_4084_ = v___x_4155_;
v___y_4085_ = v___y_4136_;
v___y_4086_ = v___y_4137_;
v___y_4087_ = v___y_4138_;
v___y_4088_ = v___y_4139_;
v___y_4089_ = v___y_4140_;
v___y_4090_ = v___y_4142_;
v___y_4091_ = v___y_4143_;
v___y_4092_ = v___x_4153_;
v___y_4093_ = v___y_4144_;
v___y_4094_ = v___y_4146_;
v___y_4095_ = v___y_4147_;
v___y_4096_ = v___x_4158_;
v___y_4097_ = v___x_4161_;
goto v___jp_4076_;
}
}
}
v___jp_4162_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; size_t v_sz_4189_; lean_object* v___x_4190_; size_t v_sz_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4176_ = lean_array_get_size(v_a_4174_);
v___x_4177_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_a_4174_, v___x_3965_, v___x_4176_);
v___x_4178_ = 0;
v___x_4179_ = l_Lean_SourceInfo_fromRef(v___y_4172_, v___x_4178_);
lean_dec(v___y_4172_);
v___x_4180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_4181_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__4));
v___x_4182_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__5));
v___x_4183_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__7));
lean_inc_n(v___x_4179_, 3);
v___x_4184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4179_);
lean_ctor_set(v___x_4184_, 1, v___x_4181_);
v___x_4185_ = l_Lean_Syntax_node1(v___x_4179_, v___x_4183_, v___x_4184_);
v___x_4186_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_4187_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_4188_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_4189_ = lean_array_size(v___y_4170_);
lean_inc_ref(v___y_4170_);
v___x_4190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_4189_, v___y_4168_, v___y_4170_);
v_sz_4191_ = lean_array_size(v___x_4190_);
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_4191_, v___y_4168_, v___x_4190_);
v___x_4193_ = l_Array_append___redArg(v___x_4188_, v___x_4192_);
lean_dec_ref(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4179_);
lean_ctor_set(v___x_4194_, 1, v___x_4187_);
lean_ctor_set(v___x_4194_, 2, v___x_4193_);
if (lean_obj_tag(v___y_4167_) == 1)
{
lean_object* v_val_4195_; lean_object* v___x_4196_; 
v_val_4195_ = lean_ctor_get(v___y_4167_, 0);
lean_inc(v_val_4195_);
lean_dec_ref(v___y_4167_);
v___x_4196_ = l_Array_mkArray1___redArg(v_val_4195_);
v___y_4130_ = v___x_4179_;
v___y_4131_ = v___x_4182_;
v___y_4132_ = v___y_4164_;
v___y_4133_ = v___y_4163_;
v___y_4134_ = v_a_4175_;
v___y_4135_ = v___x_4180_;
v___y_4136_ = v___y_4169_;
v___y_4137_ = v___y_4170_;
v___y_4138_ = v___x_4185_;
v___y_4139_ = v___y_4171_;
v___y_4140_ = v___x_4177_;
v___y_4141_ = v___y_4165_;
v___y_4142_ = v___y_4166_;
v___y_4143_ = v___x_4188_;
v___y_4144_ = v___x_4187_;
v___y_4145_ = v___x_4194_;
v___y_4146_ = v_a_4174_;
v___y_4147_ = v___y_4168_;
v___y_4148_ = v___x_4186_;
v___y_4149_ = v___y_4173_;
v___y_4150_ = v___x_4196_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4197_; 
lean_dec(v___y_4167_);
v___x_4197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_4130_ = v___x_4179_;
v___y_4131_ = v___x_4182_;
v___y_4132_ = v___y_4164_;
v___y_4133_ = v___y_4163_;
v___y_4134_ = v_a_4175_;
v___y_4135_ = v___x_4180_;
v___y_4136_ = v___y_4169_;
v___y_4137_ = v___y_4170_;
v___y_4138_ = v___x_4185_;
v___y_4139_ = v___y_4171_;
v___y_4140_ = v___x_4177_;
v___y_4141_ = v___y_4165_;
v___y_4142_ = v___y_4166_;
v___y_4143_ = v___x_4188_;
v___y_4144_ = v___x_4187_;
v___y_4145_ = v___x_4194_;
v___y_4146_ = v_a_4174_;
v___y_4147_ = v___y_4168_;
v___y_4148_ = v___x_4186_;
v___y_4149_ = v___y_4173_;
v___y_4150_ = v___x_4197_;
goto v___jp_4129_;
}
}
v___jp_4198_:
{
if (lean_obj_tag(v___y_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v_a_4212_; 
v_a_4211_ = lean_ctor_get(v___y_4210_, 0);
lean_inc(v_a_4211_);
v_a_4212_ = lean_ctor_get(v___y_4210_, 1);
lean_inc(v_a_4212_);
lean_dec_ref(v___y_4210_);
v___y_4163_ = v___y_4200_;
v___y_4164_ = v___y_4199_;
v___y_4165_ = v___y_4201_;
v___y_4166_ = v___y_4202_;
v___y_4167_ = v___y_4203_;
v___y_4168_ = v___y_4204_;
v___y_4169_ = v___y_4205_;
v___y_4170_ = v___y_4206_;
v___y_4171_ = v___y_4208_;
v___y_4172_ = v___y_4207_;
v___y_4173_ = v___y_4209_;
v_a_4174_ = v_a_4211_;
v_a_4175_ = v_a_4212_;
goto v___jp_4162_;
}
else
{
lean_object* v_a_4213_; lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec(v___x_4009_);
lean_dec(v___x_3966_);
v_a_4213_ = lean_ctor_get(v___y_4210_, 0);
v_a_4214_ = lean_ctor_get(v___y_4210_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___y_4210_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___y_4210_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_inc(v_a_4213_);
lean_dec(v___y_4210_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4213_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
v___jp_4222_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4236_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_4235_);
v___x_4237_ = lean_array_get_size(v___x_4236_);
v___x_4238_ = lean_nat_dec_lt(v___x_3965_, v___x_4237_);
if (v___x_4238_ == 0)
{
lean_dec_ref(v___x_4236_);
v___y_4163_ = v___y_4224_;
v___y_4164_ = v___y_4223_;
v___y_4165_ = v___y_4235_;
v___y_4166_ = v___y_4226_;
v___y_4167_ = v___y_4227_;
v___y_4168_ = v___y_4228_;
v___y_4169_ = v___y_4229_;
v___y_4170_ = v___y_4230_;
v___y_4171_ = v___y_4233_;
v___y_4172_ = v___y_4232_;
v___y_4173_ = v___y_4234_;
v_a_4174_ = v___y_4225_;
v_a_4175_ = v___y_4231_;
goto v___jp_4162_;
}
else
{
uint8_t v___x_4239_; 
v___x_4239_ = lean_nat_dec_le(v___x_4237_, v___x_4237_);
if (v___x_4239_ == 0)
{
if (v___x_4238_ == 0)
{
lean_dec_ref(v___x_4236_);
v___y_4163_ = v___y_4224_;
v___y_4164_ = v___y_4223_;
v___y_4165_ = v___y_4235_;
v___y_4166_ = v___y_4226_;
v___y_4167_ = v___y_4227_;
v___y_4168_ = v___y_4228_;
v___y_4169_ = v___y_4229_;
v___y_4170_ = v___y_4230_;
v___y_4171_ = v___y_4233_;
v___y_4172_ = v___y_4232_;
v___y_4173_ = v___y_4234_;
v_a_4174_ = v___y_4225_;
v_a_4175_ = v___y_4231_;
goto v___jp_4162_;
}
else
{
size_t v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = lean_usize_of_nat(v___x_4237_);
v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v___x_4236_, v___y_4228_, v___x_4240_, v___y_4225_, v___y_4224_, v___y_4231_);
lean_dec_ref(v___x_4236_);
v___y_4199_ = v___y_4223_;
v___y_4200_ = v___y_4224_;
v___y_4201_ = v___y_4235_;
v___y_4202_ = v___y_4226_;
v___y_4203_ = v___y_4227_;
v___y_4204_ = v___y_4228_;
v___y_4205_ = v___y_4229_;
v___y_4206_ = v___y_4230_;
v___y_4207_ = v___y_4232_;
v___y_4208_ = v___y_4233_;
v___y_4209_ = v___y_4234_;
v___y_4210_ = v___x_4241_;
goto v___jp_4198_;
}
}
else
{
size_t v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_usize_of_nat(v___x_4237_);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v___x_4236_, v___y_4228_, v___x_4242_, v___y_4225_, v___y_4224_, v___y_4231_);
lean_dec_ref(v___x_4236_);
v___y_4199_ = v___y_4223_;
v___y_4200_ = v___y_4224_;
v___y_4201_ = v___y_4235_;
v___y_4202_ = v___y_4226_;
v___y_4203_ = v___y_4227_;
v___y_4204_ = v___y_4228_;
v___y_4205_ = v___y_4229_;
v___y_4206_ = v___y_4230_;
v___y_4207_ = v___y_4232_;
v___y_4208_ = v___y_4233_;
v___y_4209_ = v___y_4234_;
v___y_4210_ = v___x_4243_;
goto v___jp_4198_;
}
}
}
v___jp_4244_:
{
size_t v_sz_4258_; lean_object* v___x_4259_; 
v_sz_4258_ = lean_array_size(v___y_4257_);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_4258_, v___y_4250_, v___y_4257_, v___y_4246_, v___y_4255_);
if (lean_obj_tag(v___x_4259_) == 0)
{
if (lean_obj_tag(v___y_4248_) == 0)
{
lean_object* v_a_4260_; lean_object* v_a_4261_; lean_object* v___x_4262_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
v_a_4261_ = lean_ctor_get(v___x_4259_, 1);
lean_inc(v_a_4261_);
lean_dec_ref(v___x_4259_);
v___x_4262_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4223_ = v___y_4245_;
v___y_4224_ = v___y_4246_;
v___y_4225_ = v_a_4260_;
v___y_4226_ = v___y_4247_;
v___y_4227_ = v___y_4249_;
v___y_4228_ = v___y_4250_;
v___y_4229_ = v___y_4251_;
v___y_4230_ = v___y_4252_;
v___y_4231_ = v_a_4261_;
v___y_4232_ = v___y_4254_;
v___y_4233_ = v___y_4253_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v___x_4262_;
goto v___jp_4222_;
}
else
{
lean_object* v_a_4263_; lean_object* v_a_4264_; lean_object* v_val_4265_; 
v_a_4263_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4263_);
v_a_4264_ = lean_ctor_get(v___x_4259_, 1);
lean_inc(v_a_4264_);
lean_dec_ref(v___x_4259_);
v_val_4265_ = lean_ctor_get(v___y_4248_, 0);
lean_inc(v_val_4265_);
lean_dec_ref(v___y_4248_);
v___y_4223_ = v___y_4245_;
v___y_4224_ = v___y_4246_;
v___y_4225_ = v_a_4263_;
v___y_4226_ = v___y_4247_;
v___y_4227_ = v___y_4249_;
v___y_4228_ = v___y_4250_;
v___y_4229_ = v___y_4251_;
v___y_4230_ = v___y_4252_;
v___y_4231_ = v_a_4264_;
v___y_4232_ = v___y_4254_;
v___y_4233_ = v___y_4253_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v_val_4265_;
goto v___jp_4222_;
}
}
else
{
lean_object* v_a_4266_; lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v___y_4256_);
lean_dec(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___x_4009_);
lean_dec(v___x_3966_);
v_a_4266_ = lean_ctor_get(v___x_4259_, 0);
v_a_4267_ = lean_ctor_get(v___x_4259_, 1);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4259_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_inc(v_a_4266_);
lean_dec(v___x_4259_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4266_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
v___jp_4277_:
{
lean_object* v_methods_4285_; lean_object* v_quotContext_4286_; lean_object* v_currMacroScope_4287_; lean_object* v_currRecDepth_4288_; lean_object* v_maxRecDepth_4289_; lean_object* v_ref_4290_; lean_object* v_bs_4291_; lean_object* v_ref_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v_methods_4285_ = lean_ctor_get(v___y_4283_, 0);
v_quotContext_4286_ = lean_ctor_get(v___y_4283_, 1);
v_currMacroScope_4287_ = lean_ctor_get(v___y_4283_, 2);
v_currRecDepth_4288_ = lean_ctor_get(v___y_4283_, 3);
v_maxRecDepth_4289_ = lean_ctor_get(v___y_4283_, 4);
v_ref_4290_ = lean_ctor_get(v___y_4283_, 5);
v_bs_4291_ = l_Lean_Syntax_getArgs(v___x_4276_);
lean_dec(v___x_4276_);
v_ref_4292_ = l_Lean_replaceRef(v_tk_4007_, v_ref_4290_);
lean_dec(v_tk_4007_);
lean_inc(v_ref_4292_);
lean_inc(v_maxRecDepth_4289_);
lean_inc(v_currRecDepth_4288_);
lean_inc(v_currMacroScope_4287_);
lean_inc(v_quotContext_4286_);
lean_inc(v_methods_4285_);
v___x_4293_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4293_, 0, v_methods_4285_);
lean_ctor_set(v___x_4293_, 1, v_quotContext_4286_);
lean_ctor_set(v___x_4293_, 2, v_currMacroScope_4287_);
lean_ctor_set(v___x_4293_, 3, v_currRecDepth_4288_);
lean_ctor_set(v___x_4293_, 4, v_maxRecDepth_4289_);
lean_ctor_set(v___x_4293_, 5, v_ref_4292_);
v___x_4294_ = l_Lake_expandBinders(v_bs_4291_, v___x_4293_, v___y_4284_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; size_t v_sz_4300_; size_t v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
v_a_4296_ = lean_ctor_get(v___x_4294_, 1);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4294_);
v___x_4297_ = lean_unsigned_to_nat(7u);
v___x_4298_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4297_);
lean_dec(v_stx_3958_);
v___x_4299_ = l_Lean_Syntax_getArg(v___x_4009_, v___x_3965_);
v_sz_4300_ = lean_array_size(v_a_4295_);
v___x_4301_ = ((size_t)0ULL);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_4300_, v___x_4301_, v_a_4295_);
lean_inc(v___x_4299_);
v___x_4303_ = l_Lean_Syntax_mkApp(v___x_4299_, v___x_4302_);
if (lean_obj_tag(v_fs_x3f_4282_) == 0)
{
lean_object* v___x_4304_; 
v___x_4304_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4245_ = v___x_4298_;
v___y_4246_ = v___x_4293_;
v___y_4247_ = v___x_4303_;
v___y_4248_ = v___y_4278_;
v___y_4249_ = v___y_4279_;
v___y_4250_ = v___x_4301_;
v___y_4251_ = v_ctor_x3f_4281_;
v___y_4252_ = v_bs_4291_;
v___y_4253_ = v___x_4299_;
v___y_4254_ = v_ref_4292_;
v___y_4255_ = v_a_4296_;
v___y_4256_ = v___y_4280_;
v___y_4257_ = v___x_4304_;
goto v___jp_4244_;
}
else
{
lean_object* v_val_4305_; 
v_val_4305_ = lean_ctor_get(v_fs_x3f_4282_, 0);
lean_inc(v_val_4305_);
lean_dec_ref(v_fs_x3f_4282_);
v___y_4245_ = v___x_4298_;
v___y_4246_ = v___x_4293_;
v___y_4247_ = v___x_4303_;
v___y_4248_ = v___y_4278_;
v___y_4249_ = v___y_4279_;
v___y_4250_ = v___x_4301_;
v___y_4251_ = v_ctor_x3f_4281_;
v___y_4252_ = v_bs_4291_;
v___y_4253_ = v___x_4299_;
v___y_4254_ = v_ref_4292_;
v___y_4255_ = v_a_4296_;
v___y_4256_ = v___y_4280_;
v___y_4257_ = v_val_4305_;
goto v___jp_4244_;
}
}
else
{
lean_object* v_a_4306_; lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref(v___x_4293_);
lean_dec(v_ref_4292_);
lean_dec_ref(v_bs_4291_);
lean_dec(v_fs_x3f_4282_);
lean_dec(v_ctor_x3f_4281_);
lean_dec(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec(v___x_4009_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v_a_4306_ = lean_ctor_get(v___x_4294_, 0);
v_a_4307_ = lean_ctor_get(v___x_4294_, 1);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4294_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_inc(v_a_4306_);
lean_dec(v___x_4294_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4306_);
lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
v___jp_4315_:
{
lean_object* v___x_4323_; lean_object* v_fs_x3f_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4323_ = l_Lean_Syntax_getArg(v___y_4316_, v___x_4008_);
lean_dec(v___y_4316_);
v_fs_x3f_4324_ = l_Lean_Syntax_getArgs(v___x_4323_);
lean_dec(v___x_4323_);
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v_ctor_x3f_4320_);
v___x_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4326_, 0, v_fs_x3f_4324_);
v___y_4278_ = v___y_4317_;
v___y_4279_ = v___y_4318_;
v___y_4280_ = v___y_4319_;
v_ctor_x3f_4281_ = v___x_4325_;
v_fs_x3f_4282_ = v___x_4326_;
v___y_4283_ = v___y_4321_;
v___y_4284_ = v___y_4322_;
goto v___jp_4277_;
}
v___jp_4327_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4333_ = lean_unsigned_to_nat(6u);
v___x_4334_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4333_);
v___x_4335_ = l_Lean_Syntax_isNone(v___x_4334_);
if (v___x_4335_ == 0)
{
uint8_t v___x_4336_; 
lean_inc(v___x_4334_);
v___x_4336_ = l_Lean_Syntax_matchesNull(v___x_4334_, v___x_4275_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec(v___x_4334_);
lean_dec(v_xty_x3f_4330_);
lean_dec(v_ps_x3f_4329_);
lean_dec(v___y_4328_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4337_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4338_ = l_Lean_Macro_throwError___redArg(v___x_4337_, v___y_4331_, v___y_4332_);
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4339_ = l_Lean_Syntax_getArg(v___x_4334_, v___x_3965_);
v___x_4340_ = ((lean_object*)(l_Lake_configDecl___closed__45));
v___x_4341_ = l_Lean_Syntax_isOfKind(v___x_4339_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
lean_dec(v___x_4334_);
lean_dec(v_xty_x3f_4330_);
lean_dec(v_ps_x3f_4329_);
lean_dec(v___y_4328_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4342_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4343_ = l_Lean_Macro_throwError___redArg(v___x_4342_, v___y_4331_, v___y_4332_);
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4344_ = l_Lean_Syntax_getArg(v___x_4334_, v___x_3971_);
v___x_4345_ = l_Lean_Syntax_isNone(v___x_4344_);
if (v___x_4345_ == 0)
{
uint8_t v___x_4346_; 
lean_inc(v___x_4344_);
v___x_4346_ = l_Lean_Syntax_matchesNull(v___x_4344_, v___x_3971_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
lean_dec(v___x_4344_);
lean_dec(v___x_4334_);
lean_dec(v_xty_x3f_4330_);
lean_dec(v_ps_x3f_4329_);
lean_dec(v___y_4328_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4347_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4348_ = l_Lean_Macro_throwError___redArg(v___x_4347_, v___y_4331_, v___y_4332_);
return v___x_4348_;
}
else
{
lean_object* v_ctor_x3f_4349_; lean_object* v___x_4350_; 
v_ctor_x3f_4349_ = l_Lean_Syntax_getArg(v___x_4344_, v___x_3965_);
lean_dec(v___x_4344_);
v___x_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_ctor_x3f_4349_);
v___y_4316_ = v___x_4334_;
v___y_4317_ = v_ps_x3f_4329_;
v___y_4318_ = v___y_4328_;
v___y_4319_ = v_xty_x3f_4330_;
v_ctor_x3f_4320_ = v___x_4350_;
v___y_4321_ = v___y_4331_;
v___y_4322_ = v___y_4332_;
goto v___jp_4315_;
}
}
else
{
lean_object* v___x_4351_; 
lean_dec(v___x_4344_);
v___x_4351_ = lean_box(0);
v___y_4316_ = v___x_4334_;
v___y_4317_ = v_ps_x3f_4329_;
v___y_4318_ = v___y_4328_;
v___y_4319_ = v_xty_x3f_4330_;
v_ctor_x3f_4320_ = v___x_4351_;
v___y_4321_ = v___y_4331_;
v___y_4322_ = v___y_4332_;
goto v___jp_4315_;
}
}
}
}
else
{
lean_object* v___x_4352_; 
lean_dec(v___x_4334_);
v___x_4352_ = lean_box(0);
v___y_4278_ = v_ps_x3f_4329_;
v___y_4279_ = v___y_4328_;
v___y_4280_ = v_xty_x3f_4330_;
v_ctor_x3f_4281_ = v___x_4352_;
v_fs_x3f_4282_ = v___x_4352_;
v___y_4283_ = v___y_4331_;
v___y_4284_ = v___y_4332_;
goto v___jp_4277_;
}
}
v___jp_4353_:
{
lean_object* v_ps_x3f_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_ps_x3f_4359_ = l_Lean_Syntax_getArgs(v___y_4354_);
lean_dec(v___y_4354_);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v_ps_x3f_4359_);
v___x_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4361_, 0, v_xty_x3f_4356_);
v___y_4328_ = v___y_4355_;
v_ps_x3f_4329_ = v___x_4360_;
v_xty_x3f_4330_ = v___x_4361_;
v___y_4331_ = v___y_4357_;
v___y_4332_ = v___y_4358_;
goto v___jp_4327_;
}
v___jp_4362_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4366_ = lean_unsigned_to_nat(5u);
v___x_4367_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4366_);
v___x_4368_ = l_Lean_Syntax_isNone(v___x_4367_);
if (v___x_4368_ == 0)
{
uint8_t v___x_4369_; 
lean_inc(v___x_4367_);
v___x_4369_ = l_Lean_Syntax_matchesNull(v___x_4367_, v___x_3971_);
if (v___x_4369_ == 0)
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
lean_dec(v___x_4367_);
lean_dec(v_ty_x3f_4363_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4370_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4371_ = l_Lean_Macro_throwError___redArg(v___x_4370_, v___y_4364_, v___y_4365_);
return v___x_4371_;
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4372_ = l_Lean_Syntax_getArg(v___x_4367_, v___x_3965_);
lean_dec(v___x_4367_);
v___x_4373_ = ((lean_object*)(l_Lake_configDecl___closed__33));
lean_inc(v___x_4372_);
v___x_4374_ = l_Lean_Syntax_isOfKind(v___x_4372_, v___x_4373_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
lean_dec(v___x_4372_);
lean_dec(v_ty_x3f_4363_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4375_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4376_ = l_Lean_Macro_throwError___redArg(v___x_4375_, v___y_4364_, v___y_4365_);
return v___x_4376_;
}
else
{
lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4377_ = l_Lean_Syntax_getArg(v___x_4372_, v___x_3971_);
v___x_4378_ = l_Lean_Syntax_getArg(v___x_4372_, v___x_4008_);
lean_dec(v___x_4372_);
v___x_4379_ = l_Lean_Syntax_isNone(v___x_4378_);
if (v___x_4379_ == 0)
{
uint8_t v___x_4380_; 
lean_inc(v___x_4378_);
v___x_4380_ = l_Lean_Syntax_matchesNull(v___x_4378_, v___x_3971_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec(v___x_4378_);
lean_dec(v___x_4377_);
lean_dec(v_ty_x3f_4363_);
lean_dec(v___x_4276_);
lean_dec(v___x_4009_);
lean_dec(v_tk_4007_);
lean_dec(v___x_3966_);
lean_dec(v_stx_3958_);
v___x_4381_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4382_ = l_Lean_Macro_throwError___redArg(v___x_4381_, v___y_4364_, v___y_4365_);
return v___x_4382_;
}
else
{
lean_object* v_xty_x3f_4383_; lean_object* v___x_4384_; 
v_xty_x3f_4383_ = l_Lean_Syntax_getArg(v___x_4378_, v___x_3965_);
lean_dec(v___x_4378_);
v___x_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4384_, 0, v_xty_x3f_4383_);
v___y_4354_ = v___x_4377_;
v___y_4355_ = v_ty_x3f_4363_;
v_xty_x3f_4356_ = v___x_4384_;
v___y_4357_ = v___y_4364_;
v___y_4358_ = v___y_4365_;
goto v___jp_4353_;
}
}
else
{
lean_object* v___x_4385_; 
lean_dec(v___x_4378_);
v___x_4385_ = lean_box(0);
v___y_4354_ = v___x_4377_;
v___y_4355_ = v_ty_x3f_4363_;
v_xty_x3f_4356_ = v___x_4385_;
v___y_4357_ = v___y_4364_;
v___y_4358_ = v___y_4365_;
goto v___jp_4353_;
}
}
}
}
else
{
lean_object* v___x_4386_; 
lean_dec(v___x_4367_);
v___x_4386_ = lean_box(0);
v___y_4328_ = v_ty_x3f_4363_;
v_ps_x3f_4329_ = v___x_4386_;
v_xty_x3f_4330_ = v___x_4386_;
v___y_4331_ = v___y_4364_;
v___y_4332_ = v___y_4365_;
goto v___jp_4327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___boxed(lean_object* v_stx_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lake_expandConfigDecl(v_stx_4396_, v_a_4397_, v_a_4398_);
lean_dec_ref(v_a_4397_);
return v_res_4399_;
}
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
