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
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instEmptyCollection"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instConfigInfo"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "instConfigFields"};
static const lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0 = (const lean_object*)&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(lean_object*);
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_fields"};
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
static const lean_string_object l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expected at least one field name"};
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
v___x_288_ = l_Array_mkArray0___redArg();
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
uint8_t v___x_78957__boxed_367_; lean_object* v_res_368_; 
v___x_78957__boxed_367_ = lean_unbox(v___x_363_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_78957__boxed_367_, v_____do__lift_364_, v___y_365_, v___y_366_);
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
lean_inc_ref(v___y_499_);
v___x_517_ = l_Array_append___redArg(v___y_499_, v___y_516_);
lean_dec_ref(v___y_516_);
lean_inc_n(v___y_504_, 4);
lean_inc_n(v___y_503_, 18);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v___y_503_);
lean_ctor_set(v___x_518_, 1, v___y_504_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_inc_n(v___y_505_, 11);
lean_inc(v___y_506_);
v___x_519_ = l_Lean_Syntax_node7(v___y_503_, v___y_506_, v___y_505_, v___y_505_, v___x_518_, v___y_505_, v___y_505_, v___y_505_, v___y_505_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_513_, 4);
lean_inc_ref_n(v___y_508_, 9);
lean_inc_ref_n(v___y_512_, 9);
v___x_521_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___y_513_, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_524_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_523_);
v___x_525_ = l_Lean_Syntax_node1(v___y_503_, v___x_524_, v___y_505_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_503_);
lean_ctor_set(v___x_526_, 1, v___x_520_);
v___x_527_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_528_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___y_513_, v___x_527_);
v___x_529_ = l_Lean_Syntax_node2(v___y_503_, v___x_528_, v___y_500_, v___y_505_);
v___x_530_ = l_Lean_Syntax_node1(v___y_503_, v___y_504_, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_532_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___y_513_, v___x_531_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_534_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_503_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_538_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_537_);
v___x_539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_515_, 2);
lean_inc_n(v___y_501_, 2);
v___x_541_ = l_Lean_addMacroScope(v___y_501_, v___x_540_, v___y_515_);
v___x_542_ = lean_box(0);
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_544_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_544_, 0, v___y_503_);
lean_ctor_set(v___x_544_, 1, v___x_539_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
lean_ctor_set(v___x_544_, 3, v___x_543_);
lean_inc(v_type_478_);
lean_inc(v___x_497_);
lean_inc(v_structTy_477_);
v___x_545_ = l_Lean_Syntax_node3(v___y_503_, v___y_504_, v_structTy_477_, v___x_497_, v_type_478_);
v___x_546_ = l_Lean_Syntax_node2(v___y_503_, v___x_538_, v___x_544_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___y_503_, v___x_534_, v___x_536_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node2(v___y_503_, v___x_532_, v___y_505_, v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_550_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___y_513_, v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v___y_503_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_554_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_503_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
lean_inc(v___x_479_);
v___x_557_ = l_Lean_Syntax_node1(v___y_503_, v___y_504_, v___x_479_);
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_503_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Syntax_node3(v___y_503_, v___x_554_, v___x_556_, v___x_557_, v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_563_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_561_, v___x_562_);
v___x_564_ = l_Lean_Syntax_node2(v___y_503_, v___x_563_, v___y_505_, v___y_505_);
v_ref_565_ = l_Lean_replaceRef(v_fields_491_, v___y_502_);
lean_inc(v_ref_565_);
lean_inc(v___y_511_);
lean_inc(v___y_510_);
lean_inc(v___y_507_);
v___x_566_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_566_, 0, v___y_507_);
lean_ctor_set(v___x_566_, 1, v___y_501_);
lean_ctor_set(v___x_566_, 2, v___y_515_);
lean_ctor_set(v___x_566_, 3, v___y_510_);
lean_ctor_set(v___x_566_, 4, v___y_511_);
lean_ctor_set(v___x_566_, 5, v_ref_565_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_489_, v_ref_565_, v___x_566_, v___y_514_);
lean_dec_ref_known(v___x_566_, 6);
lean_dec(v_ref_565_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_n(v_a_568_, 30);
v_a_569_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_567_, 2);
lean_inc(v___y_505_);
lean_inc_n(v___y_503_, 2);
v___x_570_ = l_Lean_Syntax_node4(v___y_503_, v___x_550_, v___x_552_, v___x_560_, v___x_564_, v___y_505_);
v___x_571_ = l_Lean_Syntax_node6(v___y_503_, v___x_521_, v___x_525_, v___x_526_, v___y_505_, v___x_530_, v___x_548_, v___x_570_);
lean_inc(v___y_509_);
v___x_572_ = l_Lean_Syntax_node2(v___y_503_, v___y_509_, v___x_519_, v___x_571_);
v___x_573_ = lean_array_push(v_cmds_490_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_508_, 7);
lean_inc_ref_n(v___y_512_, 7);
v___x_575_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v_a_568_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_515_, 5);
lean_inc_n(v___y_501_, 5);
v___x_580_ = l_Lean_addMacroScope(v___y_501_, v___x_579_, v___y_515_);
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v_a_568_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_542_);
lean_inc_ref(v___y_499_);
lean_inc_n(v___y_504_, 7);
v___x_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_582_, 0, v_a_568_);
lean_ctor_set(v___x_582_, 1, v___y_504_);
lean_ctor_set(v___x_582_, 2, v___y_499_);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_584_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v_a_568_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_588_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_590_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_592_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_591_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_595_ = l_Lean_addMacroScope(v___y_501_, v___x_594_, v___y_515_);
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v_a_568_);
lean_ctor_set(v___x_596_, 1, v___x_593_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_ctor_set(v___x_596_, 3, v___x_542_);
lean_inc_ref_n(v___x_582_, 17);
lean_inc_n(v___x_592_, 2);
v___x_597_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_596_, v___x_582_);
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_599_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_598_);
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_568_);
lean_ctor_set(v___x_600_, 1, v___x_551_);
lean_inc_ref_n(v___x_600_, 2);
lean_inc_n(v___x_599_, 2);
v___x_601_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_582_, v___x_497_);
v___x_602_ = l_Lean_Syntax_node3(v_a_568_, v___y_504_, v___x_582_, v___x_582_, v___x_601_);
lean_inc_n(v___x_590_, 2);
v___x_603_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_597_, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_606_ = l_Lean_addMacroScope(v___y_501_, v___x_605_, v___y_515_);
v___x_607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_607_, 0, v_a_568_);
lean_ctor_set(v___x_607_, 1, v___x_604_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
lean_ctor_set(v___x_607_, 3, v___x_542_);
v___x_608_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_607_, v___x_582_);
lean_inc(v___x_480_);
v___x_609_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_582_, v___x_480_);
v___x_610_ = l_Lean_Syntax_node3(v_a_568_, v___y_504_, v___x_582_, v___x_582_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_608_, v___x_610_);
v___x_612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_614_ = l_Lean_addMacroScope(v___y_501_, v___x_613_, v___y_515_);
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v_a_568_);
lean_ctor_set(v___x_615_, 1, v___x_612_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_ctor_set(v___x_615_, 3, v___x_542_);
v___x_616_ = l_Lean_Syntax_node2(v_a_568_, v___x_592_, v___x_615_, v___x_582_);
v___x_617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_618_ = l_Lean_Syntax_node3(v_a_568_, v___x_599_, v___x_600_, v___x_582_, v___x_617_);
v___x_619_ = l_Lean_Syntax_node3(v_a_568_, v___y_504_, v___x_582_, v___x_582_, v___x_618_);
v___x_620_ = l_Lean_Syntax_node2(v_a_568_, v___x_590_, v___x_616_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node6(v_a_568_, v___y_504_, v___x_603_, v___x_582_, v___x_611_, v___x_582_, v___x_620_, v___x_582_);
v___x_622_ = l_Lean_Syntax_node1(v_a_568_, v___x_588_, v___x_621_);
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_624_ = l_Lean_Name_mkStr4(v___y_512_, v___y_508_, v___x_522_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node1(v_a_568_, v___x_624_, v___x_582_);
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v_a_568_);
lean_ctor_set(v___x_626_, 1, v___x_535_);
v___x_627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_629_ = l_Lean_addMacroScope(v___y_501_, v___x_628_, v___y_515_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_631_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_631_, 0, v_a_568_);
lean_ctor_set(v___x_631_, 1, v___x_627_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
lean_ctor_set(v___x_631_, 3, v___x_630_);
v___x_632_ = l_Lean_Syntax_node2(v_a_568_, v___y_504_, v___x_626_, v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_634_, 0, v_a_568_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_Syntax_node6(v_a_568_, v___x_584_, v___x_586_, v___x_582_, v___x_622_, v___x_625_, v___x_632_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node1(v_a_568_, v___y_504_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node5(v_a_568_, v___x_575_, v_fields_491_, v___x_577_, v___x_581_, v___x_582_, v___x_636_);
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
lean_dec_ref_known(v___x_552_, 2);
lean_dec(v___x_550_);
lean_dec(v___x_548_);
lean_dec(v___x_530_);
lean_dec_ref_known(v___x_526_, 2);
lean_dec(v___x_525_);
lean_dec(v___x_521_);
lean_dec(v___x_519_);
lean_dec(v___y_505_);
lean_dec(v___y_503_);
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
lean_dec_ref_known(v___x_661_, 2);
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
v___y_499_ = v___x_671_;
v___y_500_ = v___x_664_;
v___y_501_ = v_quotContext_656_;
v___y_502_ = v_ref_660_;
v___y_503_ = v_a_662_;
v___y_504_ = v___x_670_;
v___y_505_ = v___x_672_;
v___y_506_ = v___x_669_;
v___y_507_ = v_methods_655_;
v___y_508_ = v___x_666_;
v___y_509_ = v___x_668_;
v___y_510_ = v_currRecDepth_658_;
v___y_511_ = v_maxRecDepth_659_;
v___y_512_ = v___x_665_;
v___y_513_ = v___x_667_;
v___y_514_ = v_a_663_;
v___y_515_ = v_currMacroScope_657_;
v___y_516_ = v___x_674_;
goto v___jp_498_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_499_ = v___x_671_;
v___y_500_ = v___x_664_;
v___y_501_ = v_quotContext_656_;
v___y_502_ = v_ref_660_;
v___y_503_ = v_a_662_;
v___y_504_ = v___x_670_;
v___y_505_ = v___x_672_;
v___y_506_ = v___x_669_;
v___y_507_ = v_methods_655_;
v___y_508_ = v___x_666_;
v___y_509_ = v___x_668_;
v___y_510_ = v_currRecDepth_658_;
v___y_511_ = v_maxRecDepth_659_;
v___y_512_ = v___x_665_;
v___y_513_ = v___x_667_;
v___y_514_ = v_a_663_;
v___y_515_ = v_currMacroScope_657_;
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
lean_inc_ref(v___y_747_);
v___x_758_ = l_Array_append___redArg(v___y_747_, v___y_757_);
lean_dec_ref(v___y_757_);
lean_inc_n(v___y_748_, 4);
lean_inc_n(v___y_753_, 18);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___y_753_);
lean_ctor_set(v___x_759_, 1, v___y_748_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_inc_n(v___y_744_, 11);
lean_inc(v___y_743_);
v___x_760_ = l_Lean_Syntax_node7(v___y_753_, v___y_743_, v___y_744_, v___y_744_, v___x_759_, v___y_744_, v___y_744_, v___y_744_, v___y_744_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_749_, 4);
lean_inc_ref_n(v___y_755_, 9);
lean_inc_ref_n(v___y_745_, 9);
v___x_762_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___y_749_, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_765_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___y_753_, v___x_765_, v___y_744_);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_753_);
lean_ctor_set(v___x_767_, 1, v___x_761_);
v___x_768_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_769_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___y_749_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___y_753_, v___x_769_, v___y_750_, v___y_744_);
v___x_771_ = l_Lean_Syntax_node1(v___y_753_, v___y_748_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_773_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___y_749_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_775_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_753_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_779_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_778_);
v___x_780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_754_, 2);
lean_inc_n(v___y_756_, 2);
v___x_782_ = l_Lean_addMacroScope(v___y_756_, v___x_781_, v___y_754_);
v___x_783_ = lean_box(0);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_785_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_785_, 0, v___y_753_);
lean_ctor_set(v___x_785_, 1, v___x_780_);
lean_ctor_set(v___x_785_, 2, v___x_782_);
lean_ctor_set(v___x_785_, 3, v___x_784_);
lean_inc(v_type_719_);
lean_inc(v___x_738_);
lean_inc(v_structTy_718_);
v___x_786_ = l_Lean_Syntax_node3(v___y_753_, v___y_748_, v_structTy_718_, v___x_738_, v_type_719_);
v___x_787_ = l_Lean_Syntax_node2(v___y_753_, v___x_779_, v___x_785_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node2(v___y_753_, v___x_775_, v___x_777_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___y_753_, v___x_773_, v___y_744_, v___x_788_);
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_791_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___y_749_, v___x_790_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___y_753_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_795_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_794_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_753_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_inc(v___x_720_);
v___x_798_ = l_Lean_Syntax_node1(v___y_753_, v___y_748_, v___x_720_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___y_753_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_Syntax_node3(v___y_753_, v___x_795_, v___x_797_, v___x_798_, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_804_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_802_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node2(v___y_753_, v___x_804_, v___y_744_, v___y_744_);
v_ref_806_ = l_Lean_replaceRef(v_fields_732_, v___y_740_);
lean_inc(v_ref_806_);
lean_inc(v___y_742_);
lean_inc(v___y_741_);
lean_inc(v___y_752_);
v___x_807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_807_, 0, v___y_752_);
lean_ctor_set(v___x_807_, 1, v___y_756_);
lean_ctor_set(v___x_807_, 2, v___y_754_);
lean_ctor_set(v___x_807_, 3, v___y_741_);
lean_ctor_set(v___x_807_, 4, v___y_742_);
lean_ctor_set(v___x_807_, 5, v_ref_806_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_730_, v_ref_806_, v___x_807_, v___y_751_);
lean_dec_ref_known(v___x_807_, 6);
lean_dec(v_ref_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_n(v_a_809_, 30);
v_a_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_808_, 2);
lean_inc(v___y_744_);
lean_inc_n(v___y_753_, 2);
v___x_811_ = l_Lean_Syntax_node4(v___y_753_, v___x_791_, v___x_793_, v___x_801_, v___x_805_, v___y_744_);
v___x_812_ = l_Lean_Syntax_node6(v___y_753_, v___x_762_, v___x_766_, v___x_767_, v___y_744_, v___x_771_, v___x_789_, v___x_811_);
lean_inc(v___y_746_);
v___x_813_ = l_Lean_Syntax_node2(v___y_753_, v___y_746_, v___x_760_, v___x_812_);
v___x_814_ = lean_array_push(v_cmds_731_, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_755_, 7);
lean_inc_ref_n(v___y_745_, 7);
v___x_816_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_815_);
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_818_, 0, v_a_809_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_754_, 5);
lean_inc_n(v___y_756_, 5);
v___x_821_ = l_Lean_addMacroScope(v___y_756_, v___x_820_, v___y_754_);
v___x_822_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_822_, 0, v_a_809_);
lean_ctor_set(v___x_822_, 1, v___x_819_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
lean_ctor_set(v___x_822_, 3, v___x_783_);
lean_inc_ref(v___y_747_);
lean_inc_n(v___y_748_, 7);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v_a_809_);
lean_ctor_set(v___x_823_, 1, v___y_748_);
lean_ctor_set(v___x_823_, 2, v___y_747_);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_825_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_824_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v_a_809_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_829_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_831_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_830_);
v___x_832_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_833_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_832_);
v___x_834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_836_ = l_Lean_addMacroScope(v___y_756_, v___x_835_, v___y_754_);
v___x_837_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_837_, 0, v_a_809_);
lean_ctor_set(v___x_837_, 1, v___x_834_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
lean_ctor_set(v___x_837_, 3, v___x_783_);
lean_inc_ref_n(v___x_823_, 17);
lean_inc_n(v___x_833_, 2);
v___x_838_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_837_, v___x_823_);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_840_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_839_);
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_809_);
lean_ctor_set(v___x_841_, 1, v___x_792_);
lean_inc_ref_n(v___x_841_, 2);
lean_inc_n(v___x_840_, 2);
v___x_842_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_823_, v___x_738_);
v___x_843_ = l_Lean_Syntax_node3(v_a_809_, v___y_748_, v___x_823_, v___x_823_, v___x_842_);
lean_inc_n(v___x_831_, 2);
v___x_844_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_838_, v___x_843_);
v___x_845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_847_ = l_Lean_addMacroScope(v___y_756_, v___x_846_, v___y_754_);
v___x_848_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_848_, 0, v_a_809_);
lean_ctor_set(v___x_848_, 1, v___x_845_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
lean_ctor_set(v___x_848_, 3, v___x_783_);
v___x_849_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_848_, v___x_823_);
lean_inc(v___x_721_);
v___x_850_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_823_, v___x_721_);
v___x_851_ = l_Lean_Syntax_node3(v_a_809_, v___y_748_, v___x_823_, v___x_823_, v___x_850_);
v___x_852_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_849_, v___x_851_);
v___x_853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_855_ = l_Lean_addMacroScope(v___y_756_, v___x_854_, v___y_754_);
v___x_856_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_856_, 0, v_a_809_);
lean_ctor_set(v___x_856_, 1, v___x_853_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_783_);
v___x_857_ = l_Lean_Syntax_node2(v_a_809_, v___x_833_, v___x_856_, v___x_823_);
v___x_858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_859_ = l_Lean_Syntax_node3(v_a_809_, v___x_840_, v___x_841_, v___x_823_, v___x_858_);
v___x_860_ = l_Lean_Syntax_node3(v_a_809_, v___y_748_, v___x_823_, v___x_823_, v___x_859_);
v___x_861_ = l_Lean_Syntax_node2(v_a_809_, v___x_831_, v___x_857_, v___x_860_);
v___x_862_ = l_Lean_Syntax_node6(v_a_809_, v___y_748_, v___x_844_, v___x_823_, v___x_852_, v___x_823_, v___x_861_, v___x_823_);
v___x_863_ = l_Lean_Syntax_node1(v_a_809_, v___x_829_, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_865_ = l_Lean_Name_mkStr4(v___y_745_, v___y_755_, v___x_763_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node1(v_a_809_, v___x_865_, v___x_823_);
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v_a_809_);
lean_ctor_set(v___x_867_, 1, v___x_776_);
v___x_868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_870_ = l_Lean_addMacroScope(v___y_756_, v___x_869_, v___y_754_);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_872_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_872_, 0, v_a_809_);
lean_ctor_set(v___x_872_, 1, v___x_868_);
lean_ctor_set(v___x_872_, 2, v___x_870_);
lean_ctor_set(v___x_872_, 3, v___x_871_);
v___x_873_ = l_Lean_Syntax_node2(v_a_809_, v___y_748_, v___x_867_, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_809_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_Syntax_node6(v_a_809_, v___x_825_, v___x_827_, v___x_823_, v___x_863_, v___x_866_, v___x_873_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node1(v_a_809_, v___y_748_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node5(v_a_809_, v___x_816_, v_fields_732_, v___x_818_, v___x_822_, v___x_823_, v___x_877_);
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
lean_dec_ref_known(v___x_793_, 2);
lean_dec(v___x_791_);
lean_dec(v___x_789_);
lean_dec(v___x_771_);
lean_dec_ref_known(v___x_767_, 2);
lean_dec(v___x_766_);
lean_dec(v___x_762_);
lean_dec(v___x_760_);
lean_dec(v___y_753_);
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
lean_dec_ref_known(v___x_902_, 2);
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
v___y_740_ = v_ref_901_;
v___y_741_ = v_currRecDepth_899_;
v___y_742_ = v_maxRecDepth_900_;
v___y_743_ = v___x_910_;
v___y_744_ = v___x_913_;
v___y_745_ = v___x_906_;
v___y_746_ = v___x_909_;
v___y_747_ = v___x_912_;
v___y_748_ = v___x_911_;
v___y_749_ = v___x_908_;
v___y_750_ = v___x_905_;
v___y_751_ = v_a_904_;
v___y_752_ = v_methods_896_;
v___y_753_ = v_a_903_;
v___y_754_ = v_currMacroScope_898_;
v___y_755_ = v___x_907_;
v___y_756_ = v_quotContext_897_;
v___y_757_ = v___x_915_;
goto v___jp_739_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_740_ = v_ref_901_;
v___y_741_ = v_currRecDepth_899_;
v___y_742_ = v_maxRecDepth_900_;
v___y_743_ = v___x_910_;
v___y_744_ = v___x_913_;
v___y_745_ = v___x_906_;
v___y_746_ = v___x_909_;
v___y_747_ = v___x_912_;
v___y_748_ = v___x_911_;
v___y_749_ = v___x_908_;
v___y_750_ = v___x_905_;
v___y_751_ = v_a_904_;
v___y_752_ = v_methods_896_;
v___y_753_ = v_a_903_;
v___y_754_ = v_currMacroScope_898_;
v___y_755_ = v___x_907_;
v___y_756_ = v_quotContext_897_;
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
lean_object* v_a_1125_; lean_object* v_a_1126_; uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1130_ == 0)
{
lean_object* v_cmds_1131_; lean_object* v_fields_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1884_; 
v_cmds_1131_ = lean_ctor_get(v_b_1121_, 0);
v_fields_1132_ = lean_ctor_get(v_b_1121_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_b_1121_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1134_ = v_b_1121_;
v_isShared_1135_ = v_isSharedCheck_1884_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_fields_1132_);
lean_inc(v_cmds_1131_);
lean_dec(v_b_1121_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1884_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v_id_1137_; lean_object* v_ids_1138_; lean_object* v_type_1139_; lean_object* v_defVal_1140_; uint8_t v_parent_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___x_1642_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1848_; uint8_t v___x_1868_; 
v___x_1136_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
v_id_1137_ = lean_ctor_get(v___x_1136_, 2);
v_ids_1138_ = lean_ctor_get(v___x_1136_, 3);
v_type_1139_ = lean_ctor_get(v___x_1136_, 4);
v_defVal_1140_ = lean_ctor_get(v___x_1136_, 5);
v_parent_1141_ = lean_ctor_get_uint8(v___x_1136_, sizeof(void*)*7);
v___x_1642_ = l_Lean_TSyntax_getId(v_id_1137_);
v___x_1868_ = l_Lean_Name_hasMacroScopes(v___x_1642_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_inc(v___x_1642_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1117_, v___x_1642_);
v___y_1848_ = v___x_1869_;
goto v___jp_1847_;
}
else
{
lean_object* v_view_1870_; lean_object* v_name_1871_; lean_object* v_imported_1872_; lean_object* v_ctx_1873_; lean_object* v_scopes_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1883_; 
lean_inc(v___x_1642_);
v_view_1870_ = l_Lean_extractMacroScopes(v___x_1642_);
v_name_1871_ = lean_ctor_get(v_view_1870_, 0);
v_imported_1872_ = lean_ctor_get(v_view_1870_, 1);
v_ctx_1873_ = lean_ctor_get(v_view_1870_, 2);
v_scopes_1874_ = lean_ctor_get(v_view_1870_, 3);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_view_1870_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1876_ = v_view_1870_;
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_scopes_1874_);
lean_inc(v_ctx_1873_);
lean_inc(v_imported_1872_);
lean_inc(v_name_1871_);
lean_dec(v_view_1870_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1117_, v_name_1871_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_imported_1872_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_ctx_1873_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_scopes_1874_);
v___x_1880_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_MacroScopesView_review(v___x_1880_);
v___y_1848_ = v___x_1881_;
goto v___jp_1847_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_ref_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_inc_ref(v___y_1165_);
v___x_1183_ = l_Array_append___redArg(v___y_1165_, v___y_1182_);
lean_dec_ref(v___y_1182_);
lean_inc_n(v___y_1148_, 4);
lean_inc_n(v___y_1154_, 18);
v___x_1184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1184_, 0, v___y_1154_);
lean_ctor_set(v___x_1184_, 1, v___y_1148_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_inc_n(v___y_1175_, 11);
lean_inc(v___y_1177_);
v___x_1185_ = l_Lean_Syntax_node7(v___y_1154_, v___y_1177_, v___y_1175_, v___y_1175_, v___x_1184_, v___y_1175_, v___y_1175_, v___y_1175_, v___y_1175_);
v___x_1186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1149_, 3);
lean_inc_ref_n(v___y_1179_, 6);
lean_inc_ref_n(v___y_1174_, 6);
v___x_1187_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1149_, v___x_1186_);
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1147_, 2);
v___x_1189_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1147_, v___x_1188_);
v___x_1190_ = l_Lean_Syntax_node1(v___y_1154_, v___x_1189_, v___y_1175_);
v___x_1191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1154_);
lean_ctor_set(v___x_1191_, 1, v___x_1186_);
v___x_1192_ = l_Lean_Syntax_node2(v___y_1154_, v___y_1145_, v___y_1163_, v___y_1175_);
v___x_1193_ = l_Lean_Syntax_node1(v___y_1154_, v___y_1148_, v___x_1192_);
v___x_1194_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1195_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1149_, v___x_1194_);
lean_inc_ref(v___y_1153_);
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1154_);
lean_ctor_set(v___x_1196_, 1, v___y_1153_);
v___x_1197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1198_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1164_, 2);
lean_inc_n(v___y_1167_, 2);
v___x_1200_ = l_Lean_addMacroScope(v___y_1167_, v___x_1199_, v___y_1164_);
lean_inc_ref(v___y_1143_);
v___x_1201_ = l_Lean_Name_mkStr2(v___y_1143_, v___x_1197_);
lean_inc(v___y_1156_);
lean_inc(v___x_1201_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___y_1156_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_inc(v___y_1180_);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___y_1180_);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1202_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1206_, 0, v___y_1154_);
lean_ctor_set(v___x_1206_, 1, v___x_1198_);
lean_ctor_set(v___x_1206_, 2, v___x_1200_);
lean_ctor_set(v___x_1206_, 3, v___x_1205_);
lean_inc(v_type_1139_);
lean_inc(v___y_1159_);
lean_inc(v_structTy_1114_);
v___x_1207_ = l_Lean_Syntax_node3(v___y_1154_, v___y_1148_, v_structTy_1114_, v___y_1159_, v_type_1139_);
v___x_1208_ = l_Lean_Syntax_node2(v___y_1154_, v___y_1166_, v___x_1206_, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node2(v___y_1154_, v___y_1150_, v___x_1196_, v___x_1208_);
v___x_1210_ = l_Lean_Syntax_node2(v___y_1154_, v___x_1195_, v___y_1175_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1212_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1149_, v___x_1211_);
lean_inc_ref(v___y_1181_);
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1154_);
lean_ctor_set(v___x_1213_, 1, v___y_1181_);
v___x_1214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1215_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1147_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1154_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_inc(v___y_1151_);
v___x_1218_ = l_Lean_Syntax_node1(v___y_1154_, v___y_1148_, v___y_1151_);
v___x_1219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1154_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node3(v___y_1154_, v___x_1215_, v___x_1217_, v___x_1218_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1224_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___x_1222_, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node2(v___y_1154_, v___x_1224_, v___y_1175_, v___y_1175_);
v_ref_1226_ = l_Lean_replaceRef(v_fields_1132_, v___y_1144_);
lean_inc(v_ref_1226_);
lean_inc(v___y_1160_);
lean_inc(v___y_1152_);
lean_inc(v___y_1176_);
v___x_1227_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1227_, 0, v___y_1176_);
lean_ctor_set(v___x_1227_, 1, v___y_1167_);
lean_ctor_set(v___x_1227_, 2, v___y_1164_);
lean_ctor_set(v___x_1227_, 3, v___y_1152_);
lean_ctor_set(v___x_1227_, 4, v___y_1160_);
lean_ctor_set(v___x_1227_, 5, v_ref_1226_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1130_, v_ref_1226_, v___x_1227_, v___y_1161_);
lean_dec_ref_known(v___x_1227_, 6);
lean_dec(v_ref_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_n(v_a_1229_, 30);
v_a_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1228_, 2);
lean_inc(v___y_1175_);
lean_inc_n(v___y_1154_, 2);
v___x_1231_ = l_Lean_Syntax_node4(v___y_1154_, v___x_1212_, v___x_1213_, v___x_1221_, v___x_1225_, v___y_1175_);
v___x_1232_ = l_Lean_Syntax_node6(v___y_1154_, v___x_1187_, v___x_1190_, v___x_1191_, v___y_1175_, v___x_1193_, v___x_1210_, v___x_1231_);
lean_inc(v___y_1170_);
v___x_1233_ = l_Lean_Syntax_node2(v___y_1154_, v___y_1170_, v___x_1185_, v___x_1232_);
v___x_1234_ = lean_array_push(v___y_1158_, v___x_1233_);
v___x_1235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1179_);
lean_inc_ref(v___y_1174_);
v___x_1236_ = l_Lean_Name_mkStr4(v___y_1174_, v___y_1179_, v___y_1147_, v___x_1235_);
v___x_1237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1229_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1164_, 5);
lean_inc_n(v___y_1167_, 5);
v___x_1241_ = l_Lean_addMacroScope(v___y_1167_, v___x_1240_, v___y_1164_);
lean_inc_n(v___y_1180_, 5);
v___x_1242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1242_, 0, v_a_1229_);
lean_ctor_set(v___x_1242_, 1, v___x_1239_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
lean_ctor_set(v___x_1242_, 3, v___y_1180_);
lean_inc_ref(v___y_1165_);
lean_inc_n(v___y_1148_, 7);
v___x_1243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1243_, 0, v_a_1229_);
lean_ctor_set(v___x_1243_, 1, v___y_1148_);
lean_ctor_set(v___x_1243_, 2, v___y_1165_);
lean_inc_ref(v___y_1171_);
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_a_1229_);
lean_ctor_set(v___x_1244_, 1, v___y_1171_);
v___x_1245_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1247_ = l_Lean_addMacroScope(v___y_1167_, v___x_1246_, v___y_1164_);
v___x_1248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1229_);
lean_ctor_set(v___x_1248_, 1, v___x_1245_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
lean_ctor_set(v___x_1248_, 3, v___y_1180_);
lean_inc_ref_n(v___x_1243_, 17);
lean_inc_n(v___y_1178_, 2);
v___x_1249_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1178_, v___x_1248_, v___x_1243_);
lean_inc_ref(v___y_1181_);
v___x_1250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1229_);
lean_ctor_set(v___x_1250_, 1, v___y_1181_);
lean_inc_ref_n(v___x_1250_, 2);
lean_inc_n(v___y_1162_, 2);
v___x_1251_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1162_, v___x_1250_, v___x_1243_, v___y_1159_);
v___x_1252_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1148_, v___x_1243_, v___x_1243_, v___x_1251_);
lean_inc_n(v___y_1157_, 2);
v___x_1253_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1157_, v___x_1249_, v___x_1252_);
v___x_1254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1256_ = l_Lean_addMacroScope(v___y_1167_, v___x_1255_, v___y_1164_);
v___x_1257_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1229_);
lean_ctor_set(v___x_1257_, 1, v___x_1254_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
lean_ctor_set(v___x_1257_, 3, v___y_1180_);
v___x_1258_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1178_, v___x_1257_, v___x_1243_);
lean_inc(v___y_1169_);
v___x_1259_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1162_, v___x_1250_, v___x_1243_, v___y_1169_);
v___x_1260_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1148_, v___x_1243_, v___x_1243_, v___x_1259_);
v___x_1261_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1157_, v___x_1258_, v___x_1260_);
v___x_1262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_1264_ = l_Lean_addMacroScope(v___y_1167_, v___x_1263_, v___y_1164_);
v___x_1265_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1229_);
lean_ctor_set(v___x_1265_, 1, v___x_1262_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
lean_ctor_set(v___x_1265_, 3, v___y_1180_);
v___x_1266_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1178_, v___x_1265_, v___x_1243_);
v___x_1267_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_1268_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1162_, v___x_1250_, v___x_1243_, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node3(v_a_1229_, v___y_1148_, v___x_1243_, v___x_1243_, v___x_1268_);
v___x_1270_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1157_, v___x_1266_, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_node6(v_a_1229_, v___y_1148_, v___x_1253_, v___x_1243_, v___x_1261_, v___x_1243_, v___x_1270_, v___x_1243_);
v___x_1272_ = l_Lean_Syntax_node1(v_a_1229_, v___y_1146_, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_node1(v_a_1229_, v___y_1173_, v___x_1243_);
lean_inc_ref(v___y_1153_);
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1229_);
lean_ctor_set(v___x_1274_, 1, v___y_1153_);
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1278_ = l_Lean_addMacroScope(v___y_1167_, v___x_1277_, v___y_1164_);
lean_inc_ref(v___y_1143_);
v___x_1279_ = l_Lean_Name_mkStr2(v___y_1143_, v___x_1275_);
lean_inc(v___y_1156_);
lean_inc(v___x_1279_);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___y_1156_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___y_1180_);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1280_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1229_);
lean_ctor_set(v___x_1284_, 1, v___x_1276_);
lean_ctor_set(v___x_1284_, 2, v___x_1278_);
lean_ctor_set(v___x_1284_, 3, v___x_1283_);
v___x_1285_ = l_Lean_Syntax_node2(v_a_1229_, v___y_1148_, v___x_1274_, v___x_1284_);
lean_inc_ref(v___y_1168_);
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1229_);
lean_ctor_set(v___x_1286_, 1, v___y_1168_);
v___x_1287_ = l_Lean_Syntax_node6(v_a_1229_, v___y_1155_, v___x_1244_, v___x_1243_, v___x_1272_, v___x_1273_, v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node1(v_a_1229_, v___y_1148_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node5(v_a_1229_, v___x_1236_, v_fields_1132_, v___x_1238_, v___x_1242_, v___x_1243_, v___x_1288_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1289_);
lean_ctor_set(v___x_1134_, 0, v___x_1234_);
v___x_1291_ = v___x_1134_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_dec_lt(v___x_1292_, v___y_1172_);
if (v___x_1293_ == 0)
{
lean_dec(v___y_1172_);
lean_dec(v___y_1169_);
lean_dec(v___y_1151_);
v_a_1125_ = v___x_1291_;
v_a_1126_ = v_a_1230_;
goto v___jp_1124_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_of_nat(v___y_1172_);
lean_dec(v___y_1172_);
lean_inc(v_vis_x3f_1116_);
lean_inc(v_type_1139_);
lean_inc(v_structTy_1114_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1114_, v_type_1139_, v___y_1151_, v___y_1169_, v_vis_x3f_1116_, v_structId_1117_, v_ids_1138_, v___x_1294_, v___x_1295_, v___x_1291_, v___y_1122_, v_a_1230_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_a_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1296_, 2);
v_a_1125_ = v_a_1297_;
v_a_1126_ = v_a_1298_;
goto v___jp_1124_;
}
else
{
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v___x_1225_);
lean_dec(v___x_1221_);
lean_dec_ref_known(v___x_1213_, 2);
lean_dec(v___x_1212_);
lean_dec(v___x_1210_);
lean_dec(v___x_1193_);
lean_dec_ref_known(v___x_1191_, 2);
lean_dec(v___x_1190_);
lean_dec(v___x_1187_);
lean_dec(v___x_1185_);
lean_dec(v___y_1178_);
lean_dec(v___y_1175_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v___y_1169_);
lean_dec(v___y_1162_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_del_object(v___x_1134_);
lean_dec(v_fields_1132_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1300_ = lean_ctor_get(v___x_1228_, 0);
v_a_1301_ = lean_ctor_get(v___x_1228_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1228_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_inc(v_a_1300_);
lean_dec(v___x_1228_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1300_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
v___jp_1309_:
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1130_, v___y_1311_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_a_1349_, 2);
v_a_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1348_, 2);
v___x_1351_ = l_Lean_mkIdentFrom(v___y_1340_, v___y_1347_, v___x_1130_);
lean_dec(v___y_1340_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1315_);
v___x_1352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1349_);
lean_ctor_set(v___x_1352_, 1, v___y_1315_);
lean_ctor_set(v___x_1352_, 2, v___y_1330_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1354_; 
v_val_1353_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1353_);
v___x_1354_ = l_Array_mkArray1___redArg(v_val_1353_);
v___y_1143_ = v___y_1310_;
v___y_1144_ = v___y_1311_;
v___y_1145_ = v___y_1312_;
v___y_1146_ = v___y_1313_;
v___y_1147_ = v___y_1314_;
v___y_1148_ = v___y_1315_;
v___y_1149_ = v___y_1317_;
v___y_1150_ = v___y_1318_;
v___y_1151_ = v___y_1320_;
v___y_1152_ = v___y_1319_;
v___y_1153_ = v___y_1321_;
v___y_1154_ = v_a_1349_;
v___y_1155_ = v___y_1322_;
v___y_1156_ = v___y_1323_;
v___y_1157_ = v___y_1324_;
v___y_1158_ = v___y_1325_;
v___y_1159_ = v___y_1326_;
v___y_1160_ = v___y_1327_;
v___y_1161_ = v_a_1350_;
v___y_1162_ = v___y_1328_;
v___y_1163_ = v___x_1351_;
v___y_1164_ = v___y_1329_;
v___y_1165_ = v___y_1330_;
v___y_1166_ = v___y_1331_;
v___y_1167_ = v___y_1332_;
v___y_1168_ = v___y_1333_;
v___y_1169_ = v___y_1334_;
v___y_1170_ = v___y_1335_;
v___y_1171_ = v___y_1336_;
v___y_1172_ = v___y_1339_;
v___y_1173_ = v___y_1338_;
v___y_1174_ = v___y_1337_;
v___y_1175_ = v___x_1352_;
v___y_1176_ = v___y_1341_;
v___y_1177_ = v___y_1342_;
v___y_1178_ = v___y_1343_;
v___y_1179_ = v___y_1344_;
v___y_1180_ = v___y_1346_;
v___y_1181_ = v___y_1345_;
v___y_1182_ = v___x_1354_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_mk_empty_array_with_capacity(v___y_1316_);
v___y_1143_ = v___y_1310_;
v___y_1144_ = v___y_1311_;
v___y_1145_ = v___y_1312_;
v___y_1146_ = v___y_1313_;
v___y_1147_ = v___y_1314_;
v___y_1148_ = v___y_1315_;
v___y_1149_ = v___y_1317_;
v___y_1150_ = v___y_1318_;
v___y_1151_ = v___y_1320_;
v___y_1152_ = v___y_1319_;
v___y_1153_ = v___y_1321_;
v___y_1154_ = v_a_1349_;
v___y_1155_ = v___y_1322_;
v___y_1156_ = v___y_1323_;
v___y_1157_ = v___y_1324_;
v___y_1158_ = v___y_1325_;
v___y_1159_ = v___y_1326_;
v___y_1160_ = v___y_1327_;
v___y_1161_ = v_a_1350_;
v___y_1162_ = v___y_1328_;
v___y_1163_ = v___x_1351_;
v___y_1164_ = v___y_1329_;
v___y_1165_ = v___y_1330_;
v___y_1166_ = v___y_1331_;
v___y_1167_ = v___y_1332_;
v___y_1168_ = v___y_1333_;
v___y_1169_ = v___y_1334_;
v___y_1170_ = v___y_1335_;
v___y_1171_ = v___y_1336_;
v___y_1172_ = v___y_1339_;
v___y_1173_ = v___y_1338_;
v___y_1174_ = v___y_1337_;
v___y_1175_ = v___x_1352_;
v___y_1176_ = v___y_1341_;
v___y_1177_ = v___y_1342_;
v___y_1178_ = v___y_1343_;
v___y_1179_ = v___y_1344_;
v___y_1180_ = v___y_1346_;
v___y_1181_ = v___y_1345_;
v___y_1182_ = v___x_1355_;
goto v___jp_1142_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v___y_1347_);
lean_dec(v___y_1343_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1334_);
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec(v___y_1322_);
lean_dec(v___y_1320_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec(v___y_1312_);
lean_del_object(v___x_1134_);
lean_dec(v_fields_1132_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1356_ = lean_ctor_get(v___x_1348_, 0);
v_a_1357_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1348_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_inc(v_a_1356_);
lean_dec(v___x_1348_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_ref_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc_ref(v___y_1387_);
v___x_1404_ = l_Array_append___redArg(v___y_1387_, v___y_1403_);
lean_dec_ref(v___y_1403_);
lean_inc_n(v___y_1372_, 4);
lean_inc_n(v___y_1374_, 18);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1374_);
lean_ctor_set(v___x_1405_, 1, v___y_1372_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
lean_inc_n(v___y_1400_, 11);
lean_inc(v___y_1397_);
v___x_1406_ = l_Lean_Syntax_node7(v___y_1374_, v___y_1397_, v___y_1400_, v___y_1400_, v___x_1405_, v___y_1400_, v___y_1400_, v___y_1400_, v___y_1400_);
v___x_1407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1373_, 3);
lean_inc_ref_n(v___y_1399_, 6);
lean_inc_ref_n(v___y_1395_, 6);
v___x_1408_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1373_, v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1371_, 2);
v___x_1410_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1371_, v___x_1409_);
v___x_1411_ = l_Lean_Syntax_node1(v___y_1374_, v___x_1410_, v___y_1400_);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1374_);
lean_ctor_set(v___x_1412_, 1, v___x_1407_);
v___x_1413_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1368_, v___y_1369_, v___y_1400_);
v___x_1414_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1372_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1416_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1373_, v___x_1415_);
lean_inc_ref(v___y_1378_);
v___x_1417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___y_1374_);
lean_ctor_set(v___x_1417_, 1, v___y_1378_);
v___x_1418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_1419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_1420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_1386_, 2);
lean_inc_n(v___y_1389_, 2);
v___x_1421_ = l_Lean_addMacroScope(v___y_1389_, v___x_1420_, v___y_1386_);
lean_inc_ref(v___y_1366_);
v___x_1422_ = l_Lean_Name_mkStr2(v___y_1366_, v___x_1418_);
lean_inc(v___y_1381_);
lean_inc(v___x_1422_);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___y_1381_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_inc(v___y_1401_);
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___y_1401_);
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1423_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1374_);
lean_ctor_set(v___x_1427_, 1, v___x_1419_);
lean_ctor_set(v___x_1427_, 2, v___x_1421_);
lean_ctor_set(v___x_1427_, 3, v___x_1426_);
lean_inc(v_type_1139_);
lean_inc(v_structTy_1114_);
v___x_1428_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1372_, v_structTy_1114_, v_type_1139_);
lean_inc(v___y_1388_);
v___x_1429_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1388_, v___x_1427_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1375_, v___x_1417_, v___x_1429_);
v___x_1431_ = l_Lean_Syntax_node2(v___y_1374_, v___x_1416_, v___y_1400_, v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1433_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1373_, v___x_1432_);
lean_inc_ref(v___y_1402_);
v___x_1434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___y_1374_);
lean_ctor_set(v___x_1434_, 1, v___y_1402_);
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1436_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1371_, v___x_1435_);
v___x_1437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___y_1374_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1372_, v___y_1376_);
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___y_1374_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_Syntax_node3(v___y_1374_, v___x_1436_, v___x_1438_, v___x_1439_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1445_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___x_1443_, v___x_1444_);
v___x_1446_ = l_Lean_Syntax_node2(v___y_1374_, v___x_1445_, v___y_1400_, v___y_1400_);
v_ref_1447_ = l_Lean_replaceRef(v_fields_1132_, v___y_1367_);
lean_inc(v_ref_1447_);
lean_inc(v___y_1384_);
lean_inc(v___y_1377_);
lean_inc(v___y_1396_);
v___x_1448_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1396_);
lean_ctor_set(v___x_1448_, 1, v___y_1389_);
lean_ctor_set(v___x_1448_, 2, v___y_1386_);
lean_ctor_set(v___x_1448_, 3, v___y_1377_);
lean_ctor_set(v___x_1448_, 4, v___y_1384_);
lean_ctor_set(v___x_1448_, 5, v_ref_1447_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1130_, v_ref_1447_, v___x_1448_, v___y_1379_);
lean_dec_ref_known(v___x_1448_, 6);
lean_dec(v_ref_1447_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_ref_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_n(v_a_1450_, 14);
v_a_1451_ = lean_ctor_get(v___x_1449_, 1);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1449_, 2);
v___x_1452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_1371_, 2);
lean_inc_ref_n(v___y_1399_, 5);
lean_inc_ref_n(v___y_1395_, 7);
v___x_1453_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1371_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_a_1450_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_1457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_1386_, 4);
lean_inc_n(v___y_1389_, 4);
v___x_1458_ = l_Lean_addMacroScope(v___y_1389_, v___x_1457_, v___y_1386_);
lean_inc_n(v___y_1401_, 3);
v___x_1459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1459_, 0, v_a_1450_);
lean_ctor_set(v___x_1459_, 1, v___x_1456_);
lean_ctor_set(v___x_1459_, 2, v___x_1458_);
lean_ctor_set(v___x_1459_, 3, v___y_1401_);
lean_inc_ref(v___y_1387_);
lean_inc_n(v___y_1372_, 3);
v___x_1460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1450_);
lean_ctor_set(v___x_1460_, 1, v___y_1372_);
lean_ctor_set(v___x_1460_, 2, v___y_1387_);
v___x_1461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_1462_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1371_, v___x_1461_);
v___x_1463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_1464_ = l_Lean_Name_mkStr4(v___y_1395_, v___y_1399_, v___y_1371_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_1466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_a_1450_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_1468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Lean_addMacroScope(v___y_1389_, v___x_1469_, v___y_1386_);
lean_inc_ref_n(v___y_1366_, 2);
v___x_1471_ = l_Lean_Name_mkStr1(v___y_1366_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_inc_ref(v___y_1373_);
v___x_1473_ = l_Lean_Name_mkStr3(v___y_1395_, v___y_1399_, v___y_1373_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = l_Lean_Name_mkStr2(v___y_1395_, v___y_1399_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_1478_ = l_Lean_Name_mkStr2(v___y_1395_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
v___x_1480_ = l_Lean_Name_mkStr1(v___y_1395_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___y_1401_);
v___x_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1479_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1476_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1474_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1472_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1487_, 0, v_a_1450_);
lean_ctor_set(v___x_1487_, 1, v___x_1468_);
lean_ctor_set(v___x_1487_, 2, v___x_1470_);
lean_ctor_set(v___x_1487_, 3, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node1(v_a_1450_, v___x_1467_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node2(v_a_1450_, v___x_1464_, v___x_1466_, v___x_1488_);
v___x_1490_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_1491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_1492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_1493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_1494_ = l_Lean_addMacroScope(v___y_1389_, v___x_1493_, v___y_1386_);
v___x_1495_ = l_Lean_Name_mkStr3(v___y_1366_, v___x_1491_, v___x_1492_);
lean_inc(v___y_1381_);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___y_1381_);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___y_1401_);
v___x_1498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1498_, 0, v_a_1450_);
lean_ctor_set(v___x_1498_, 1, v___x_1490_);
lean_ctor_set(v___x_1498_, 2, v___x_1494_);
lean_ctor_set(v___x_1498_, 3, v___x_1497_);
lean_inc(v_type_1139_);
v___x_1499_ = l_Lean_Syntax_node1(v_a_1450_, v___y_1372_, v_type_1139_);
v___x_1500_ = l_Lean_Syntax_node2(v_a_1450_, v___y_1388_, v___x_1498_, v___x_1499_);
v___x_1501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_1502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1450_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_Syntax_node3(v_a_1450_, v___x_1462_, v___x_1489_, v___x_1500_, v___x_1502_);
v___x_1504_ = l_Lean_Syntax_node1(v_a_1450_, v___y_1372_, v___x_1503_);
lean_inc(v___x_1453_);
v___x_1505_ = l_Lean_Syntax_node5(v_a_1450_, v___x_1453_, v_fields_1132_, v___x_1455_, v___x_1459_, v___x_1460_, v___x_1504_);
v_ref_1506_ = l_Lean_replaceRef(v___x_1505_, v___y_1367_);
lean_inc(v_ref_1506_);
lean_inc(v___y_1384_);
lean_inc(v___y_1377_);
lean_inc(v___y_1396_);
v___x_1507_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1396_);
lean_ctor_set(v___x_1507_, 1, v___y_1389_);
lean_ctor_set(v___x_1507_, 2, v___y_1386_);
lean_ctor_set(v___x_1507_, 3, v___y_1377_);
lean_ctor_set(v___x_1507_, 4, v___y_1384_);
lean_ctor_set(v___x_1507_, 5, v_ref_1506_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1130_, v_ref_1506_, v___x_1507_, v_a_1451_);
lean_dec_ref_known(v___x_1507_, 6);
lean_dec(v_ref_1506_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_n(v_a_1509_, 29);
v_a_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1508_, 2);
lean_inc(v___y_1400_);
lean_inc_n(v___y_1374_, 2);
v___x_1511_ = l_Lean_Syntax_node4(v___y_1374_, v___x_1433_, v___x_1434_, v___x_1442_, v___x_1446_, v___y_1400_);
v___x_1512_ = l_Lean_Syntax_node6(v___y_1374_, v___x_1408_, v___x_1411_, v___x_1412_, v___y_1400_, v___x_1414_, v___x_1431_, v___x_1511_);
lean_inc(v___y_1392_);
v___x_1513_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1392_, v___x_1406_, v___x_1512_);
v___x_1514_ = lean_array_push(v___y_1383_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_a_1509_);
lean_ctor_set(v___x_1515_, 1, v___x_1454_);
v___x_1516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1386_, 6);
lean_inc_n(v___y_1389_, 6);
v___x_1518_ = l_Lean_addMacroScope(v___y_1389_, v___x_1517_, v___y_1386_);
lean_inc_n(v___y_1401_, 6);
v___x_1519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1509_);
lean_ctor_set(v___x_1519_, 1, v___x_1516_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
lean_ctor_set(v___x_1519_, 3, v___y_1401_);
lean_inc_ref(v___y_1387_);
lean_inc_n(v___y_1372_, 6);
v___x_1520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1509_);
lean_ctor_set(v___x_1520_, 1, v___y_1372_);
lean_ctor_set(v___x_1520_, 2, v___y_1387_);
lean_inc_ref(v___y_1393_);
v___x_1521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1509_);
lean_ctor_set(v___x_1521_, 1, v___y_1393_);
v___x_1522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1524_ = l_Lean_addMacroScope(v___y_1389_, v___x_1523_, v___y_1386_);
v___x_1525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1509_);
lean_ctor_set(v___x_1525_, 1, v___x_1522_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
lean_ctor_set(v___x_1525_, 3, v___y_1401_);
lean_inc_ref_n(v___x_1520_, 14);
lean_inc_n(v___y_1398_, 2);
v___x_1526_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1398_, v___x_1525_, v___x_1520_);
lean_inc_ref(v___y_1402_);
v___x_1527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_a_1509_);
lean_ctor_set(v___x_1527_, 1, v___y_1402_);
lean_inc_ref(v___x_1527_);
lean_inc(v___y_1385_);
v___x_1528_ = l_Lean_Syntax_node3(v_a_1509_, v___y_1385_, v___x_1527_, v___x_1520_, v___y_1391_);
v___x_1529_ = l_Lean_Syntax_node3(v_a_1509_, v___y_1372_, v___x_1520_, v___x_1520_, v___x_1528_);
lean_inc(v___x_1529_);
lean_inc_n(v___y_1382_, 2);
v___x_1530_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1382_, v___x_1526_, v___x_1529_);
v___x_1531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1533_ = l_Lean_addMacroScope(v___y_1389_, v___x_1532_, v___y_1386_);
v___x_1534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1509_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_ctor_set(v___x_1534_, 3, v___y_1401_);
v___x_1535_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1398_, v___x_1534_, v___x_1520_);
v___x_1536_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1382_, v___x_1535_, v___x_1529_);
v___x_1537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_1539_ = l_Lean_addMacroScope(v___y_1389_, v___x_1538_, v___y_1386_);
v___x_1540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1540_, 0, v_a_1509_);
lean_ctor_set(v___x_1540_, 1, v___x_1537_);
lean_ctor_set(v___x_1540_, 2, v___x_1539_);
lean_ctor_set(v___x_1540_, 3, v___y_1401_);
v___x_1541_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1398_, v___x_1540_, v___x_1520_);
v___x_1542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_1544_ = l_Lean_addMacroScope(v___y_1389_, v___x_1543_, v___y_1386_);
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_1381_, 2);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___y_1381_);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___y_1401_);
v___x_1548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1509_);
lean_ctor_set(v___x_1548_, 1, v___x_1542_);
lean_ctor_set(v___x_1548_, 2, v___x_1544_);
lean_ctor_set(v___x_1548_, 3, v___x_1547_);
v___x_1549_ = l_Lean_Syntax_node3(v_a_1509_, v___y_1385_, v___x_1527_, v___x_1520_, v___x_1548_);
v___x_1550_ = l_Lean_Syntax_node3(v_a_1509_, v___y_1372_, v___x_1520_, v___x_1520_, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1382_, v___x_1541_, v___x_1550_);
v___x_1552_ = l_Lean_Syntax_node6(v_a_1509_, v___y_1372_, v___x_1530_, v___x_1520_, v___x_1536_, v___x_1520_, v___x_1551_, v___x_1520_);
v___x_1553_ = l_Lean_Syntax_node1(v_a_1509_, v___y_1370_, v___x_1552_);
v___x_1554_ = l_Lean_Syntax_node1(v_a_1509_, v___y_1394_, v___x_1520_);
lean_inc_ref(v___y_1378_);
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_a_1509_);
lean_ctor_set(v___x_1555_, 1, v___y_1378_);
v___x_1556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1559_ = l_Lean_addMacroScope(v___y_1389_, v___x_1558_, v___y_1386_);
lean_inc_ref(v___y_1366_);
v___x_1560_ = l_Lean_Name_mkStr2(v___y_1366_, v___x_1556_);
lean_inc(v___x_1560_);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___y_1381_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___y_1401_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1561_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1509_);
lean_ctor_set(v___x_1565_, 1, v___x_1557_);
lean_ctor_set(v___x_1565_, 2, v___x_1559_);
lean_ctor_set(v___x_1565_, 3, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_node2(v_a_1509_, v___y_1372_, v___x_1555_, v___x_1565_);
lean_inc_ref(v___y_1390_);
v___x_1567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1509_);
lean_ctor_set(v___x_1567_, 1, v___y_1390_);
v___x_1568_ = l_Lean_Syntax_node6(v_a_1509_, v___y_1380_, v___x_1521_, v___x_1520_, v___x_1553_, v___x_1554_, v___x_1566_, v___x_1567_);
v___x_1569_ = l_Lean_Syntax_node1(v_a_1509_, v___y_1372_, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_node5(v_a_1509_, v___x_1453_, v___x_1505_, v___x_1515_, v___x_1519_, v___x_1520_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1514_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v_a_1125_ = v___x_1571_;
v_a_1126_ = v_a_1510_;
goto v___jp_1124_;
}
else
{
lean_object* v_a_1572_; lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v___x_1505_);
lean_dec(v___x_1453_);
lean_dec(v___x_1446_);
lean_dec(v___x_1442_);
lean_dec_ref_known(v___x_1434_, 2);
lean_dec(v___x_1433_);
lean_dec(v___x_1431_);
lean_dec(v___x_1414_);
lean_dec_ref_known(v___x_1412_, 2);
lean_dec(v___x_1411_);
lean_dec(v___x_1408_);
lean_dec(v___x_1406_);
lean_dec(v___y_1400_);
lean_dec(v___y_1398_);
lean_dec(v___y_1394_);
lean_dec(v___y_1391_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1380_);
lean_dec(v___y_1374_);
lean_dec(v___y_1370_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1572_ = lean_ctor_get(v___x_1508_, 0);
v_a_1573_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1508_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_inc(v_a_1572_);
lean_dec(v___x_1508_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v___x_1446_);
lean_dec(v___x_1442_);
lean_dec_ref_known(v___x_1434_, 2);
lean_dec(v___x_1433_);
lean_dec(v___x_1431_);
lean_dec(v___x_1414_);
lean_dec_ref_known(v___x_1412_, 2);
lean_dec(v___x_1411_);
lean_dec(v___x_1408_);
lean_dec(v___x_1406_);
lean_dec(v___y_1400_);
lean_dec(v___y_1398_);
lean_dec(v___y_1394_);
lean_dec(v___y_1391_);
lean_dec(v___y_1388_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1380_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec(v_fields_1132_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1581_ = lean_ctor_get(v___x_1449_, 0);
v_a_1582_ = lean_ctor_get(v___x_1449_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1449_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_inc(v_a_1581_);
lean_dec(v___x_1449_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
v___jp_1590_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1130_, v___y_1592_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_n(v_a_1626_, 2);
v_a_1627_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1625_, 2);
v___x_1628_ = l_Lean_mkIdentFrom(v_id_1137_, v___y_1624_, v___x_1130_);
lean_inc_ref(v___y_1609_);
lean_inc(v___y_1596_);
v___x_1629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1626_);
lean_ctor_set(v___x_1629_, 1, v___y_1596_);
lean_ctor_set(v___x_1629_, 2, v___y_1609_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1630_; lean_object* v___x_1631_; 
v_val_1630_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1630_);
v___x_1631_ = l_Array_mkArray1___redArg(v_val_1630_);
v___y_1366_ = v___y_1591_;
v___y_1367_ = v___y_1592_;
v___y_1368_ = v___y_1593_;
v___y_1369_ = v___x_1628_;
v___y_1370_ = v___y_1594_;
v___y_1371_ = v___y_1595_;
v___y_1372_ = v___y_1596_;
v___y_1373_ = v___y_1597_;
v___y_1374_ = v_a_1626_;
v___y_1375_ = v___y_1598_;
v___y_1376_ = v___y_1600_;
v___y_1377_ = v___y_1599_;
v___y_1378_ = v___y_1601_;
v___y_1379_ = v_a_1627_;
v___y_1380_ = v___y_1602_;
v___y_1381_ = v___y_1603_;
v___y_1382_ = v___y_1604_;
v___y_1383_ = v___y_1605_;
v___y_1384_ = v___y_1606_;
v___y_1385_ = v___y_1607_;
v___y_1386_ = v___y_1608_;
v___y_1387_ = v___y_1609_;
v___y_1388_ = v___y_1610_;
v___y_1389_ = v___y_1611_;
v___y_1390_ = v___y_1612_;
v___y_1391_ = v___y_1613_;
v___y_1392_ = v___y_1614_;
v___y_1393_ = v___y_1615_;
v___y_1394_ = v___y_1617_;
v___y_1395_ = v___y_1616_;
v___y_1396_ = v___y_1618_;
v___y_1397_ = v___y_1619_;
v___y_1398_ = v___y_1620_;
v___y_1399_ = v___y_1621_;
v___y_1400_ = v___x_1629_;
v___y_1401_ = v___y_1623_;
v___y_1402_ = v___y_1622_;
v___y_1403_ = v___x_1631_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1366_ = v___y_1591_;
v___y_1367_ = v___y_1592_;
v___y_1368_ = v___y_1593_;
v___y_1369_ = v___x_1628_;
v___y_1370_ = v___y_1594_;
v___y_1371_ = v___y_1595_;
v___y_1372_ = v___y_1596_;
v___y_1373_ = v___y_1597_;
v___y_1374_ = v_a_1626_;
v___y_1375_ = v___y_1598_;
v___y_1376_ = v___y_1600_;
v___y_1377_ = v___y_1599_;
v___y_1378_ = v___y_1601_;
v___y_1379_ = v_a_1627_;
v___y_1380_ = v___y_1602_;
v___y_1381_ = v___y_1603_;
v___y_1382_ = v___y_1604_;
v___y_1383_ = v___y_1605_;
v___y_1384_ = v___y_1606_;
v___y_1385_ = v___y_1607_;
v___y_1386_ = v___y_1608_;
v___y_1387_ = v___y_1609_;
v___y_1388_ = v___y_1610_;
v___y_1389_ = v___y_1611_;
v___y_1390_ = v___y_1612_;
v___y_1391_ = v___y_1613_;
v___y_1392_ = v___y_1614_;
v___y_1393_ = v___y_1615_;
v___y_1394_ = v___y_1617_;
v___y_1395_ = v___y_1616_;
v___y_1396_ = v___y_1618_;
v___y_1397_ = v___y_1619_;
v___y_1398_ = v___y_1620_;
v___y_1399_ = v___y_1621_;
v___y_1400_ = v___x_1629_;
v___y_1401_ = v___y_1623_;
v___y_1402_ = v___y_1622_;
v___y_1403_ = v___x_1632_;
goto v___jp_1365_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___y_1624_);
lean_dec(v___y_1620_);
lean_dec(v___y_1617_);
lean_dec(v___y_1613_);
lean_dec(v___y_1610_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec(v___y_1602_);
lean_dec(v___y_1600_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec(v_fields_1132_);
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v_a_1633_ = lean_ctor_get(v___x_1625_, 0);
v_a_1634_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1625_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_inc(v_a_1633_);
lean_dec(v___x_1625_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1633_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
v___jp_1643_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_inc_ref_n(v___y_1644_, 2);
v___x_1661_ = l_Array_append___redArg(v___y_1644_, v___y_1660_);
lean_dec_ref(v___y_1660_);
lean_inc_n(v___y_1648_, 19);
lean_inc_n(v___y_1657_, 69);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1657_);
lean_ctor_set(v___x_1662_, 1, v___y_1648_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
lean_inc_n(v___y_1653_, 35);
lean_inc(v___y_1655_);
v___x_1663_ = l_Lean_Syntax_node7(v___y_1657_, v___y_1655_, v___y_1653_, v___y_1653_, v___x_1662_, v___y_1653_, v___y_1653_, v___y_1653_, v___y_1653_);
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_1650_, 4);
lean_inc_ref_n(v___y_1658_, 15);
lean_inc_ref_n(v___y_1649_, 15);
v___x_1665_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___y_1650_, v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_1667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1657_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_1669_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___y_1650_, v___x_1668_);
lean_inc(v___y_1654_);
lean_inc(v___x_1669_);
v___x_1670_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1669_, v___y_1654_, v___y_1653_);
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_1672_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___y_1650_, v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_1675_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1674_);
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_1677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1657_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_1679_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1678_);
v___x_1680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_1659_, 8);
lean_inc_n(v___y_1646_, 8);
v___x_1682_ = l_Lean_addMacroScope(v___y_1646_, v___x_1681_, v___y_1659_);
v___x_1683_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_1684_ = lean_box(0);
v___x_1685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_1686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1657_);
lean_ctor_set(v___x_1686_, 1, v___x_1680_);
lean_ctor_set(v___x_1686_, 2, v___x_1682_);
lean_ctor_set(v___x_1686_, 3, v___x_1685_);
lean_inc(v_type_1139_);
lean_inc(v_structTy_1114_);
v___x_1687_ = l_Lean_Syntax_node2(v___y_1657_, v___y_1648_, v_structTy_1114_, v_type_1139_);
lean_inc_n(v___x_1679_, 2);
v___x_1688_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1679_, v___x_1686_, v___x_1687_);
lean_inc(v___x_1675_);
v___x_1689_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1675_, v___x_1677_, v___x_1688_);
v___x_1690_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1689_);
v___x_1691_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1672_, v___y_1653_, v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_1693_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___y_1650_, v___x_1692_);
v___x_1694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1657_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_1697_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1696_);
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_1699_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1698_);
v___x_1700_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_1701_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1700_);
v___x_1702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_1704_ = l_Lean_addMacroScope(v___y_1646_, v___x_1703_, v___y_1659_);
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_1706_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1706_, 0, v___y_1657_);
lean_ctor_set(v___x_1706_, 1, v___x_1702_);
lean_ctor_set(v___x_1706_, 2, v___x_1704_);
lean_ctor_set(v___x_1706_, 3, v___x_1705_);
lean_inc_n(v___x_1701_, 5);
v___x_1707_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1701_, v___x_1706_, v___y_1653_);
v___x_1708_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_1709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_1710_ = l_Lean_addMacroScope(v___y_1646_, v___x_1709_, v___y_1659_);
v___x_1711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1711_, 0, v___y_1657_);
lean_ctor_set(v___x_1711_, 1, v___x_1708_);
lean_ctor_set(v___x_1711_, 2, v___x_1710_);
lean_ctor_set(v___x_1711_, 3, v___x_1684_);
lean_inc_ref_n(v___x_1711_, 3);
v___x_1712_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1711_);
v___x_1713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_1714_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_1716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___y_1657_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_1718_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1717_);
v___x_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___y_1657_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_inc_n(v_id_1137_, 3);
v___x_1721_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1718_, v___x_1711_, v___x_1720_, v_id_1137_);
lean_inc(v___x_1721_);
lean_inc_ref_n(v___x_1716_, 5);
lean_inc_n(v___x_1714_, 6);
v___x_1722_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1721_);
lean_inc(v___x_1712_);
v___x_1723_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___x_1712_, v___y_1653_, v___x_1722_);
lean_inc_n(v___x_1699_, 6);
v___x_1724_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1707_, v___x_1723_);
v___x_1725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_1727_ = l_Lean_addMacroScope(v___y_1646_, v___x_1726_, v___y_1659_);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_1729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1729_, 0, v___y_1657_);
lean_ctor_set(v___x_1729_, 1, v___x_1725_);
lean_ctor_set(v___x_1729_, 2, v___x_1727_);
lean_ctor_set(v___x_1729_, 3, v___x_1728_);
v___x_1730_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1701_, v___x_1729_, v___y_1653_);
v___x_1731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_1732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_1733_ = l_Lean_addMacroScope(v___y_1646_, v___x_1732_, v___y_1659_);
v___x_1734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1734_, 0, v___y_1657_);
lean_ctor_set(v___x_1734_, 1, v___x_1731_);
lean_ctor_set(v___x_1734_, 2, v___x_1733_);
lean_ctor_set(v___x_1734_, 3, v___x_1684_);
lean_inc_ref(v___x_1734_);
v___x_1735_ = l_Lean_Syntax_node2(v___y_1657_, v___y_1648_, v___x_1734_, v___x_1711_);
v___x_1736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_1737_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1736_);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_1739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1657_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_1741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___y_1657_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_Syntax_node2(v___y_1657_, v___y_1648_, v___x_1712_, v___x_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Lean_SourceInfo_fromRef(v___x_1743_, v___x_1130_);
lean_inc(v___x_1744_);
v___x_1745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___y_1648_);
lean_ctor_set(v___x_1745_, 2, v___y_1644_);
v___x_1746_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1701_, v_id_1137_, v___x_1745_);
v___x_1747_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1734_);
v___x_1748_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___y_1653_, v___y_1653_, v___x_1747_);
lean_inc(v___x_1746_);
v___x_1749_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1746_, v___x_1748_);
v___x_1750_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1749_);
lean_inc_n(v___x_1697_, 3);
v___x_1751_ = l_Lean_Syntax_node1(v___y_1657_, v___x_1697_, v___x_1750_);
v___x_1752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_1753_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1752_);
lean_inc(v___x_1753_);
v___x_1754_ = l_Lean_Syntax_node1(v___y_1657_, v___x_1753_, v___y_1653_);
v___x_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___y_1657_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
lean_inc_ref(v___x_1756_);
lean_inc(v___x_1754_);
lean_inc(v___x_1742_);
lean_inc_ref(v___x_1739_);
lean_inc_n(v___x_1737_, 2);
v___x_1757_ = l_Lean_Syntax_node6(v___y_1657_, v___x_1737_, v___x_1739_, v___x_1742_, v___x_1751_, v___x_1754_, v___y_1653_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1757_);
v___x_1759_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___x_1735_, v___y_1653_, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1730_, v___x_1759_);
v___x_1761_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_1762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_1763_ = l_Lean_addMacroScope(v___y_1646_, v___x_1762_, v___y_1659_);
v___x_1764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_1765_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1657_);
lean_ctor_set(v___x_1765_, 1, v___x_1761_);
lean_ctor_set(v___x_1765_, 2, v___x_1763_);
lean_ctor_set(v___x_1765_, 3, v___x_1764_);
v___x_1766_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1701_, v___x_1765_, v___y_1653_);
v___x_1767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_1768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_1769_ = l_Lean_addMacroScope(v___y_1646_, v___x_1768_, v___y_1659_);
v___x_1770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1657_);
lean_ctor_set(v___x_1770_, 1, v___x_1767_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
lean_ctor_set(v___x_1770_, 3, v___x_1684_);
lean_inc_ref(v___x_1770_);
v___x_1771_ = l_Lean_Syntax_node2(v___y_1657_, v___y_1648_, v___x_1770_, v___x_1711_);
v___x_1772_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1721_);
v___x_1773_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1679_, v___x_1770_, v___x_1772_);
v___x_1774_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1773_);
v___x_1775_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___y_1653_, v___y_1653_, v___x_1774_);
v___x_1776_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1746_, v___x_1775_);
v___x_1777_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1776_);
v___x_1778_ = l_Lean_Syntax_node1(v___y_1657_, v___x_1697_, v___x_1777_);
v___x_1779_ = l_Lean_Syntax_node6(v___y_1657_, v___x_1737_, v___x_1739_, v___x_1742_, v___x_1778_, v___x_1754_, v___y_1653_, v___x_1756_);
v___x_1780_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___x_1771_, v___y_1653_, v___x_1780_);
v___x_1782_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1766_, v___x_1781_);
v___x_1783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_1784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_1785_ = l_Lean_addMacroScope(v___y_1646_, v___x_1784_, v___y_1659_);
v___x_1786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1657_);
lean_ctor_set(v___x_1786_, 1, v___x_1783_);
lean_ctor_set(v___x_1786_, 2, v___x_1785_);
lean_ctor_set(v___x_1786_, 3, v___x_1684_);
v___x_1787_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1701_, v___x_1786_, v___y_1653_);
v___x_1788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_1789_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1657_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
v___x_1791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_1792_ = l_Lean_Name_mkStr4(v___y_1649_, v___y_1658_, v___x_1673_, v___x_1791_);
lean_inc(v___x_1115_);
v___x_1793_ = l_Lean_Syntax_node1(v___y_1657_, v___y_1648_, v___x_1115_);
v___x_1794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_1795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___y_1657_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
lean_inc(v_defVal_1140_);
v___x_1796_ = l_Lean_Syntax_node4(v___y_1657_, v___x_1792_, v___x_1793_, v___y_1653_, v___x_1795_, v_defVal_1140_);
v___x_1797_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1789_, v___x_1790_, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1714_, v___x_1716_, v___y_1653_, v___x_1797_);
v___x_1799_ = l_Lean_Syntax_node3(v___y_1657_, v___y_1648_, v___y_1653_, v___y_1653_, v___x_1798_);
v___x_1800_ = l_Lean_Syntax_node2(v___y_1657_, v___x_1699_, v___x_1787_, v___x_1799_);
v___x_1801_ = l_Lean_Syntax_node7(v___y_1657_, v___y_1648_, v___x_1724_, v___y_1653_, v___x_1760_, v___y_1653_, v___x_1782_, v___y_1653_, v___x_1800_);
v___x_1802_ = l_Lean_Syntax_node1(v___y_1657_, v___x_1697_, v___x_1801_);
v___x_1803_ = l_Lean_Syntax_node3(v___y_1657_, v___x_1693_, v___x_1695_, v___x_1802_, v___y_1653_);
v___x_1804_ = l_Lean_Syntax_node5(v___y_1657_, v___x_1665_, v___x_1667_, v___x_1670_, v___x_1691_, v___x_1803_, v___y_1653_);
lean_inc(v___y_1647_);
v___x_1805_ = l_Lean_Syntax_node2(v___y_1657_, v___y_1647_, v___x_1663_, v___x_1804_);
v___x_1806_ = lean_array_push(v_cmds_1131_, v___x_1805_);
lean_inc(v___x_1642_);
v___x_1807_ = l_Lake_Name_quoteFrom(v_id_1137_, v___x_1642_, v___x_1130_);
if (v_parent_1141_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_dec(v___x_1642_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_array_get_size(v_ids_1138_);
v___x_1810_ = lean_nat_dec_lt(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec(v___x_1807_);
lean_dec(v___x_1753_);
lean_dec(v___x_1737_);
lean_dec(v___x_1714_);
lean_dec(v___x_1701_);
lean_dec(v___x_1699_);
lean_dec(v___x_1697_);
lean_dec(v___x_1679_);
lean_dec(v___x_1675_);
lean_dec(v___x_1669_);
lean_dec(v___y_1654_);
lean_del_object(v___x_1134_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1806_);
lean_ctor_set(v___x_1811_, 1, v_fields_1132_);
v_a_1125_ = v___x_1811_;
v_a_1126_ = v___y_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1812_ = lean_array_fget_borrowed(v_ids_1138_, v___x_1808_);
v___x_1813_ = l_Lean_TSyntax_getId(v___x_1812_);
lean_inc(v___x_1813_);
lean_inc(v___x_1812_);
v___x_1814_ = l_Lake_Name_quoteFrom(v___x_1812_, v___x_1813_, v___x_1130_);
v___x_1815_ = l_Lean_Name_hasMacroScopes(v___x_1813_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1117_, v___x_1813_);
lean_inc(v___x_1812_);
v___y_1310_ = v___x_1683_;
v___y_1311_ = v___y_1645_;
v___y_1312_ = v___x_1669_;
v___y_1313_ = v___x_1697_;
v___y_1314_ = v___x_1673_;
v___y_1315_ = v___y_1648_;
v___y_1316_ = v___x_1808_;
v___y_1317_ = v___y_1650_;
v___y_1318_ = v___x_1675_;
v___y_1319_ = v___y_1652_;
v___y_1320_ = v___y_1654_;
v___y_1321_ = v___x_1676_;
v___y_1322_ = v___x_1737_;
v___y_1323_ = v___x_1684_;
v___y_1324_ = v___x_1699_;
v___y_1325_ = v___x_1806_;
v___y_1326_ = v___x_1814_;
v___y_1327_ = v___y_1656_;
v___y_1328_ = v___x_1714_;
v___y_1329_ = v___y_1659_;
v___y_1330_ = v___y_1644_;
v___y_1331_ = v___x_1679_;
v___y_1332_ = v___y_1646_;
v___y_1333_ = v___x_1755_;
v___y_1334_ = v___x_1807_;
v___y_1335_ = v___y_1647_;
v___y_1336_ = v___x_1738_;
v___y_1337_ = v___y_1649_;
v___y_1338_ = v___x_1753_;
v___y_1339_ = v___x_1809_;
v___y_1340_ = v___x_1812_;
v___y_1341_ = v___y_1651_;
v___y_1342_ = v___y_1655_;
v___y_1343_ = v___x_1701_;
v___y_1344_ = v___y_1658_;
v___y_1345_ = v___x_1715_;
v___y_1346_ = v___x_1684_;
v___y_1347_ = v___x_1816_;
goto v___jp_1309_;
}
else
{
lean_object* v_view_1817_; lean_object* v_name_1818_; lean_object* v_imported_1819_; lean_object* v_ctx_1820_; lean_object* v_scopes_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1830_; 
v_view_1817_ = l_Lean_extractMacroScopes(v___x_1813_);
v_name_1818_ = lean_ctor_get(v_view_1817_, 0);
v_imported_1819_ = lean_ctor_get(v_view_1817_, 1);
v_ctx_1820_ = lean_ctor_get(v_view_1817_, 2);
v_scopes_1821_ = lean_ctor_get(v_view_1817_, 3);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_view_1817_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1823_ = v_view_1817_;
v_isShared_1824_ = v_isSharedCheck_1830_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_scopes_1821_);
lean_inc(v_ctx_1820_);
lean_inc(v_imported_1819_);
lean_inc(v_name_1818_);
lean_dec(v_view_1817_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1830_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1117_, v_name_1818_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_imported_1819_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_ctx_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_scopes_1821_);
v___x_1827_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_MacroScopesView_review(v___x_1827_);
lean_inc(v___x_1812_);
v___y_1310_ = v___x_1683_;
v___y_1311_ = v___y_1645_;
v___y_1312_ = v___x_1669_;
v___y_1313_ = v___x_1697_;
v___y_1314_ = v___x_1673_;
v___y_1315_ = v___y_1648_;
v___y_1316_ = v___x_1808_;
v___y_1317_ = v___y_1650_;
v___y_1318_ = v___x_1675_;
v___y_1319_ = v___y_1652_;
v___y_1320_ = v___y_1654_;
v___y_1321_ = v___x_1676_;
v___y_1322_ = v___x_1737_;
v___y_1323_ = v___x_1684_;
v___y_1324_ = v___x_1699_;
v___y_1325_ = v___x_1806_;
v___y_1326_ = v___x_1814_;
v___y_1327_ = v___y_1656_;
v___y_1328_ = v___x_1714_;
v___y_1329_ = v___y_1659_;
v___y_1330_ = v___y_1644_;
v___y_1331_ = v___x_1679_;
v___y_1332_ = v___y_1646_;
v___y_1333_ = v___x_1755_;
v___y_1334_ = v___x_1807_;
v___y_1335_ = v___y_1647_;
v___y_1336_ = v___x_1738_;
v___y_1337_ = v___y_1649_;
v___y_1338_ = v___x_1753_;
v___y_1339_ = v___x_1809_;
v___y_1340_ = v___x_1812_;
v___y_1341_ = v___y_1651_;
v___y_1342_ = v___y_1655_;
v___y_1343_ = v___x_1701_;
v___y_1344_ = v___y_1658_;
v___y_1345_ = v___x_1715_;
v___y_1346_ = v___x_1684_;
v___y_1347_ = v___x_1828_;
goto v___jp_1309_;
}
}
}
}
}
else
{
uint8_t v___x_1831_; 
lean_del_object(v___x_1134_);
v___x_1831_ = l_Lean_Name_hasMacroScopes(v___x_1642_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1117_, v___x_1642_);
v___y_1591_ = v___x_1683_;
v___y_1592_ = v___y_1645_;
v___y_1593_ = v___x_1669_;
v___y_1594_ = v___x_1697_;
v___y_1595_ = v___x_1673_;
v___y_1596_ = v___y_1648_;
v___y_1597_ = v___y_1650_;
v___y_1598_ = v___x_1675_;
v___y_1599_ = v___y_1652_;
v___y_1600_ = v___y_1654_;
v___y_1601_ = v___x_1676_;
v___y_1602_ = v___x_1737_;
v___y_1603_ = v___x_1684_;
v___y_1604_ = v___x_1699_;
v___y_1605_ = v___x_1806_;
v___y_1606_ = v___y_1656_;
v___y_1607_ = v___x_1714_;
v___y_1608_ = v___y_1659_;
v___y_1609_ = v___y_1644_;
v___y_1610_ = v___x_1679_;
v___y_1611_ = v___y_1646_;
v___y_1612_ = v___x_1755_;
v___y_1613_ = v___x_1807_;
v___y_1614_ = v___y_1647_;
v___y_1615_ = v___x_1738_;
v___y_1616_ = v___y_1649_;
v___y_1617_ = v___x_1753_;
v___y_1618_ = v___y_1651_;
v___y_1619_ = v___y_1655_;
v___y_1620_ = v___x_1701_;
v___y_1621_ = v___y_1658_;
v___y_1622_ = v___x_1715_;
v___y_1623_ = v___x_1684_;
v___y_1624_ = v___x_1832_;
goto v___jp_1590_;
}
else
{
lean_object* v_view_1833_; lean_object* v_name_1834_; lean_object* v_imported_1835_; lean_object* v_ctx_1836_; lean_object* v_scopes_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1846_; 
v_view_1833_ = l_Lean_extractMacroScopes(v___x_1642_);
v_name_1834_ = lean_ctor_get(v_view_1833_, 0);
v_imported_1835_ = lean_ctor_get(v_view_1833_, 1);
v_ctx_1836_ = lean_ctor_get(v_view_1833_, 2);
v_scopes_1837_ = lean_ctor_get(v_view_1833_, 3);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_view_1833_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1839_ = v_view_1833_;
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_scopes_1837_);
lean_inc(v_ctx_1836_);
lean_inc(v_imported_1835_);
lean_inc(v_name_1834_);
lean_dec(v_view_1833_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1117_, v_name_1834_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_imported_1835_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_ctx_1836_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_scopes_1837_);
v___x_1843_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_MacroScopesView_review(v___x_1843_);
v___y_1591_ = v___x_1683_;
v___y_1592_ = v___y_1645_;
v___y_1593_ = v___x_1669_;
v___y_1594_ = v___x_1697_;
v___y_1595_ = v___x_1673_;
v___y_1596_ = v___y_1648_;
v___y_1597_ = v___y_1650_;
v___y_1598_ = v___x_1675_;
v___y_1599_ = v___y_1652_;
v___y_1600_ = v___y_1654_;
v___y_1601_ = v___x_1676_;
v___y_1602_ = v___x_1737_;
v___y_1603_ = v___x_1684_;
v___y_1604_ = v___x_1699_;
v___y_1605_ = v___x_1806_;
v___y_1606_ = v___y_1656_;
v___y_1607_ = v___x_1714_;
v___y_1608_ = v___y_1659_;
v___y_1609_ = v___y_1644_;
v___y_1610_ = v___x_1679_;
v___y_1611_ = v___y_1646_;
v___y_1612_ = v___x_1755_;
v___y_1613_ = v___x_1807_;
v___y_1614_ = v___y_1647_;
v___y_1615_ = v___x_1738_;
v___y_1616_ = v___y_1649_;
v___y_1617_ = v___x_1753_;
v___y_1618_ = v___y_1651_;
v___y_1619_ = v___y_1655_;
v___y_1620_ = v___x_1701_;
v___y_1621_ = v___y_1658_;
v___y_1622_ = v___x_1715_;
v___y_1623_ = v___x_1684_;
v___y_1624_ = v___x_1844_;
goto v___jp_1590_;
}
}
}
}
}
v___jp_1847_:
{
lean_object* v_methods_1849_; lean_object* v_quotContext_1850_; lean_object* v_currMacroScope_1851_; lean_object* v_currRecDepth_1852_; lean_object* v_maxRecDepth_1853_; lean_object* v_ref_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_methods_1849_ = lean_ctor_get(v___y_1122_, 0);
v_quotContext_1850_ = lean_ctor_get(v___y_1122_, 1);
v_currMacroScope_1851_ = lean_ctor_get(v___y_1122_, 2);
v_currRecDepth_1852_ = lean_ctor_get(v___y_1122_, 3);
v_maxRecDepth_1853_ = lean_ctor_get(v___y_1122_, 4);
v_ref_1854_ = lean_ctor_get(v___y_1122_, 5);
v___x_1855_ = l_Lean_mkIdentFrom(v_id_1137_, v___y_1848_, v___x_1130_);
v___x_1856_ = l_Lean_SourceInfo_fromRef(v_ref_1854_, v___x_1130_);
v___x_1857_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_1858_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_1859_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_1860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_1861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_1862_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_1863_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_1856_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1856_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
if (lean_obj_tag(v_vis_x3f_1116_) == 1)
{
lean_object* v_val_1865_; lean_object* v___x_1866_; 
v_val_1865_ = lean_ctor_get(v_vis_x3f_1116_, 0);
lean_inc(v_val_1865_);
v___x_1866_ = l_Array_mkArray1___redArg(v_val_1865_);
v___y_1644_ = v___x_1863_;
v___y_1645_ = v_ref_1854_;
v___y_1646_ = v_quotContext_1850_;
v___y_1647_ = v___x_1860_;
v___y_1648_ = v___x_1862_;
v___y_1649_ = v___x_1857_;
v___y_1650_ = v___x_1859_;
v___y_1651_ = v_methods_1849_;
v___y_1652_ = v_currRecDepth_1852_;
v___y_1653_ = v___x_1864_;
v___y_1654_ = v___x_1855_;
v___y_1655_ = v___x_1861_;
v___y_1656_ = v_maxRecDepth_1853_;
v___y_1657_ = v___x_1856_;
v___y_1658_ = v___x_1858_;
v___y_1659_ = v_currMacroScope_1851_;
v___y_1660_ = v___x_1866_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1644_ = v___x_1863_;
v___y_1645_ = v_ref_1854_;
v___y_1646_ = v_quotContext_1850_;
v___y_1647_ = v___x_1860_;
v___y_1648_ = v___x_1862_;
v___y_1649_ = v___x_1857_;
v___y_1650_ = v___x_1859_;
v___y_1651_ = v_methods_1849_;
v___y_1652_ = v_currRecDepth_1852_;
v___y_1653_ = v___x_1864_;
v___y_1654_ = v___x_1855_;
v___y_1655_ = v___x_1861_;
v___y_1656_ = v_maxRecDepth_1853_;
v___y_1657_ = v___x_1856_;
v___y_1658_ = v___x_1858_;
v___y_1659_ = v_currMacroScope_1851_;
v___y_1660_ = v___x_1867_;
goto v___jp_1643_;
}
}
}
}
else
{
lean_object* v___x_1885_; 
lean_dec(v_vis_x3f_1116_);
lean_dec(v___x_1115_);
lean_dec(v_structTy_1114_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_b_1121_);
lean_ctor_set(v___x_1885_, 1, v___y_1123_);
return v___x_1885_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___boxed(lean_object* v_structTy_1886_, lean_object* v___x_1887_, lean_object* v_vis_x3f_1888_, lean_object* v_structId_1889_, lean_object* v_as_1890_, lean_object* v_i_1891_, lean_object* v_stop_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
size_t v_i_boxed_1896_; size_t v_stop_boxed_1897_; lean_object* v_res_1898_; 
v_i_boxed_1896_ = lean_unbox_usize(v_i_1891_);
lean_dec(v_i_1891_);
v_stop_boxed_1897_ = lean_unbox_usize(v_stop_1892_);
lean_dec(v_stop_1892_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1886_, v___x_1887_, v_vis_x3f_1888_, v_structId_1889_, v_as_1890_, v_i_boxed_1896_, v_stop_boxed_1897_, v_b_1893_, v___y_1894_, v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_as_1890_);
lean_dec(v_structId_1889_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(lean_object* v_structTy_1899_, lean_object* v___x_1900_, lean_object* v_vis_x3f_1901_, lean_object* v_structId_1902_, lean_object* v_as_1903_, size_t v_i_1904_, size_t v_stop_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_a_1910_; lean_object* v_a_1911_; uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_eq(v_i_1904_, v_stop_1905_);
if (v___x_1915_ == 0)
{
lean_object* v_cmds_1916_; lean_object* v_fields_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_2669_; 
v_cmds_1916_ = lean_ctor_get(v_b_1906_, 0);
v_fields_1917_ = lean_ctor_get(v_b_1906_, 1);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_b_1906_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_1919_ = v_b_1906_;
v_isShared_1920_ = v_isSharedCheck_2669_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_fields_1917_);
lean_inc(v_cmds_1916_);
lean_dec(v_b_1906_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_2669_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_id_1922_; lean_object* v_ids_1923_; lean_object* v_type_1924_; lean_object* v_defVal_1925_; uint8_t v_parent_1926_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___x_2427_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2633_; uint8_t v___x_2653_; 
v___x_1921_ = lean_array_uget_borrowed(v_as_1903_, v_i_1904_);
v_id_1922_ = lean_ctor_get(v___x_1921_, 2);
v_ids_1923_ = lean_ctor_get(v___x_1921_, 3);
v_type_1924_ = lean_ctor_get(v___x_1921_, 4);
v_defVal_1925_ = lean_ctor_get(v___x_1921_, 5);
v_parent_1926_ = lean_ctor_get_uint8(v___x_1921_, sizeof(void*)*7);
v___x_2427_ = l_Lean_TSyntax_getId(v_id_1922_);
v___x_2653_ = l_Lean_Name_hasMacroScopes(v___x_2427_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_inc(v___x_2427_);
v___x_2654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1902_, v___x_2427_);
v___y_2633_ = v___x_2654_;
goto v___jp_2632_;
}
else
{
lean_object* v_view_2655_; lean_object* v_name_2656_; lean_object* v_imported_2657_; lean_object* v_ctx_2658_; lean_object* v_scopes_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2668_; 
lean_inc(v___x_2427_);
v_view_2655_ = l_Lean_extractMacroScopes(v___x_2427_);
v_name_2656_ = lean_ctor_get(v_view_2655_, 0);
v_imported_2657_ = lean_ctor_get(v_view_2655_, 1);
v_ctx_2658_ = lean_ctor_get(v_view_2655_, 2);
v_scopes_2659_ = lean_ctor_get(v_view_2655_, 3);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_view_2655_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2661_ = v_view_2655_;
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_scopes_2659_);
lean_inc(v_ctx_2658_);
lean_inc(v_imported_2657_);
lean_inc(v_name_2656_);
lean_dec(v_view_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1902_, v_name_2656_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_imported_2657_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_ctx_2658_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v_scopes_2659_);
v___x_2665_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_MacroScopesView_review(v___x_2665_);
v___y_2633_ = v___x_2666_;
goto v___jp_2632_;
}
}
}
v___jp_1927_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_ref_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_inc_ref(v___y_1960_);
v___x_1968_ = l_Array_append___redArg(v___y_1960_, v___y_1967_);
lean_dec_ref(v___y_1967_);
lean_inc_n(v___y_1935_, 4);
lean_inc_n(v___y_1933_, 18);
v___x_1969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1933_);
lean_ctor_set(v___x_1969_, 1, v___y_1935_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
lean_inc_n(v___y_1962_, 11);
lean_inc(v___y_1938_);
v___x_1970_ = l_Lean_Syntax_node7(v___y_1933_, v___y_1938_, v___y_1962_, v___y_1962_, v___x_1969_, v___y_1962_, v___y_1962_, v___y_1962_, v___y_1962_);
v___x_1971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1937_, 3);
lean_inc_ref_n(v___y_1932_, 6);
lean_inc_ref_n(v___y_1948_, 6);
v___x_1972_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1937_, v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1940_, 2);
v___x_1974_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1940_, v___x_1973_);
v___x_1975_ = l_Lean_Syntax_node1(v___y_1933_, v___x_1974_, v___y_1962_);
v___x_1976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___y_1933_);
lean_ctor_set(v___x_1976_, 1, v___x_1971_);
v___x_1977_ = l_Lean_Syntax_node2(v___y_1933_, v___y_1955_, v___y_1942_, v___y_1962_);
v___x_1978_ = l_Lean_Syntax_node1(v___y_1933_, v___y_1935_, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1980_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1937_, v___x_1979_);
lean_inc_ref(v___y_1959_);
v___x_1981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___y_1933_);
lean_ctor_set(v___x_1981_, 1, v___y_1959_);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1939_, 2);
lean_inc_n(v___y_1936_, 2);
v___x_1985_ = l_Lean_addMacroScope(v___y_1936_, v___x_1984_, v___y_1939_);
lean_inc_ref(v___y_1944_);
v___x_1986_ = l_Lean_Name_mkStr2(v___y_1944_, v___x_1982_);
lean_inc(v___y_1949_);
lean_inc(v___x_1986_);
v___x_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___y_1949_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_inc(v___y_1947_);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___y_1947_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1933_);
lean_ctor_set(v___x_1991_, 1, v___x_1983_);
lean_ctor_set(v___x_1991_, 2, v___x_1985_);
lean_ctor_set(v___x_1991_, 3, v___x_1990_);
lean_inc(v_type_1924_);
lean_inc(v___y_1956_);
lean_inc(v_structTy_1899_);
v___x_1992_ = l_Lean_Syntax_node3(v___y_1933_, v___y_1935_, v_structTy_1899_, v___y_1956_, v_type_1924_);
v___x_1993_ = l_Lean_Syntax_node2(v___y_1933_, v___y_1958_, v___x_1991_, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node2(v___y_1933_, v___y_1945_, v___x_1981_, v___x_1993_);
v___x_1995_ = l_Lean_Syntax_node2(v___y_1933_, v___x_1980_, v___y_1962_, v___x_1994_);
v___x_1996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1997_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1937_, v___x_1996_);
lean_inc_ref(v___y_1957_);
v___x_1998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1933_);
lean_ctor_set(v___x_1998_, 1, v___y_1957_);
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2000_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1940_, v___x_1999_);
v___x_2001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1933_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
lean_inc(v___y_1950_);
v___x_2003_ = l_Lean_Syntax_node1(v___y_1933_, v___y_1935_, v___y_1950_);
v___x_2004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___y_1933_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_node3(v___y_1933_, v___x_2000_, v___x_2002_, v___x_2003_, v___x_2005_);
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2009_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___x_2007_, v___x_2008_);
v___x_2010_ = l_Lean_Syntax_node2(v___y_1933_, v___x_2009_, v___y_1962_, v___y_1962_);
v_ref_2011_ = l_Lean_replaceRef(v_fields_1917_, v___y_1934_);
lean_inc(v_ref_2011_);
lean_inc(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc(v___y_1964_);
v___x_2012_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2012_, 0, v___y_1964_);
lean_ctor_set(v___x_2012_, 1, v___y_1936_);
lean_ctor_set(v___x_2012_, 2, v___y_1939_);
lean_ctor_set(v___x_2012_, 3, v___y_1929_);
lean_ctor_set(v___x_2012_, 4, v___y_1930_);
lean_ctor_set(v___x_2012_, 5, v_ref_2011_);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1915_, v_ref_2011_, v___x_2012_, v___y_1931_);
lean_dec_ref_known(v___x_2012_, 6);
lean_dec(v_ref_2011_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_n(v_a_2014_, 30);
v_a_2015_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2013_, 2);
lean_inc(v___y_1962_);
lean_inc_n(v___y_1933_, 2);
v___x_2016_ = l_Lean_Syntax_node4(v___y_1933_, v___x_1997_, v___x_1998_, v___x_2006_, v___x_2010_, v___y_1962_);
v___x_2017_ = l_Lean_Syntax_node6(v___y_1933_, v___x_1972_, v___x_1975_, v___x_1976_, v___y_1962_, v___x_1978_, v___x_1995_, v___x_2016_);
lean_inc(v___y_1952_);
v___x_2018_ = l_Lean_Syntax_node2(v___y_1933_, v___y_1952_, v___x_1970_, v___x_2017_);
v___x_2019_ = lean_array_push(v___y_1951_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1932_);
lean_inc_ref(v___y_1948_);
v___x_2021_ = l_Lean_Name_mkStr4(v___y_1948_, v___y_1932_, v___y_1940_, v___x_2020_);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_a_2014_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1939_, 5);
lean_inc_n(v___y_1936_, 5);
v___x_2026_ = l_Lean_addMacroScope(v___y_1936_, v___x_2025_, v___y_1939_);
lean_inc_n(v___y_1947_, 5);
v___x_2027_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2027_, 0, v_a_2014_);
lean_ctor_set(v___x_2027_, 1, v___x_2024_);
lean_ctor_set(v___x_2027_, 2, v___x_2026_);
lean_ctor_set(v___x_2027_, 3, v___y_1947_);
lean_inc_ref(v___y_1960_);
lean_inc_n(v___y_1935_, 7);
v___x_2028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2028_, 0, v_a_2014_);
lean_ctor_set(v___x_2028_, 1, v___y_1935_);
lean_ctor_set(v___x_2028_, 2, v___y_1960_);
lean_inc_ref(v___y_1954_);
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_a_2014_);
lean_ctor_set(v___x_2029_, 1, v___y_1954_);
v___x_2030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2032_ = l_Lean_addMacroScope(v___y_1936_, v___x_2031_, v___y_1939_);
v___x_2033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2014_);
lean_ctor_set(v___x_2033_, 1, v___x_2030_);
lean_ctor_set(v___x_2033_, 2, v___x_2032_);
lean_ctor_set(v___x_2033_, 3, v___y_1947_);
lean_inc_ref_n(v___x_2028_, 17);
lean_inc_n(v___y_1941_, 2);
v___x_2034_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1941_, v___x_2033_, v___x_2028_);
lean_inc_ref(v___y_1957_);
v___x_2035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2014_);
lean_ctor_set(v___x_2035_, 1, v___y_1957_);
lean_inc_ref_n(v___x_2035_, 2);
lean_inc_n(v___y_1966_, 2);
v___x_2036_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1966_, v___x_2035_, v___x_2028_, v___y_1956_);
v___x_2037_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1935_, v___x_2028_, v___x_2028_, v___x_2036_);
lean_inc_n(v___y_1961_, 2);
v___x_2038_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1961_, v___x_2034_, v___x_2037_);
v___x_2039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2041_ = l_Lean_addMacroScope(v___y_1936_, v___x_2040_, v___y_1939_);
v___x_2042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2014_);
lean_ctor_set(v___x_2042_, 1, v___x_2039_);
lean_ctor_set(v___x_2042_, 2, v___x_2041_);
lean_ctor_set(v___x_2042_, 3, v___y_1947_);
v___x_2043_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1941_, v___x_2042_, v___x_2028_);
lean_inc(v___y_1965_);
v___x_2044_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1966_, v___x_2035_, v___x_2028_, v___y_1965_);
v___x_2045_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1935_, v___x_2028_, v___x_2028_, v___x_2044_);
v___x_2046_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1961_, v___x_2043_, v___x_2045_);
v___x_2047_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_2049_ = l_Lean_addMacroScope(v___y_1936_, v___x_2048_, v___y_1939_);
v___x_2050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2050_, 0, v_a_2014_);
lean_ctor_set(v___x_2050_, 1, v___x_2047_);
lean_ctor_set(v___x_2050_, 2, v___x_2049_);
lean_ctor_set(v___x_2050_, 3, v___y_1947_);
v___x_2051_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1941_, v___x_2050_, v___x_2028_);
v___x_2052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_2053_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1966_, v___x_2035_, v___x_2028_, v___x_2052_);
v___x_2054_ = l_Lean_Syntax_node3(v_a_2014_, v___y_1935_, v___x_2028_, v___x_2028_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1961_, v___x_2051_, v___x_2054_);
v___x_2056_ = l_Lean_Syntax_node6(v_a_2014_, v___y_1935_, v___x_2038_, v___x_2028_, v___x_2046_, v___x_2028_, v___x_2055_, v___x_2028_);
v___x_2057_ = l_Lean_Syntax_node1(v_a_2014_, v___y_1953_, v___x_2056_);
v___x_2058_ = l_Lean_Syntax_node1(v_a_2014_, v___y_1946_, v___x_2028_);
lean_inc_ref(v___y_1959_);
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2014_);
lean_ctor_set(v___x_2059_, 1, v___y_1959_);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2061_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2063_ = l_Lean_addMacroScope(v___y_1936_, v___x_2062_, v___y_1939_);
lean_inc_ref(v___y_1944_);
v___x_2064_ = l_Lean_Name_mkStr2(v___y_1944_, v___x_2060_);
lean_inc(v___y_1949_);
lean_inc(v___x_2064_);
v___x_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___y_1949_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___y_1947_);
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2065_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2069_, 0, v_a_2014_);
lean_ctor_set(v___x_2069_, 1, v___x_2061_);
lean_ctor_set(v___x_2069_, 2, v___x_2063_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_node2(v_a_2014_, v___y_1935_, v___x_2059_, v___x_2069_);
lean_inc_ref(v___y_1928_);
v___x_2071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_a_2014_);
lean_ctor_set(v___x_2071_, 1, v___y_1928_);
v___x_2072_ = l_Lean_Syntax_node6(v_a_2014_, v___y_1963_, v___x_2029_, v___x_2028_, v___x_2057_, v___x_2058_, v___x_2070_, v___x_2071_);
v___x_2073_ = l_Lean_Syntax_node1(v_a_2014_, v___y_1935_, v___x_2072_);
v___x_2074_ = l_Lean_Syntax_node5(v_a_2014_, v___x_2021_, v_fields_1917_, v___x_2023_, v___x_2027_, v___x_2028_, v___x_2073_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_2074_);
lean_ctor_set(v___x_1919_, 0, v___x_2019_);
v___x_2076_ = v___x_1919_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = lean_nat_dec_lt(v___x_2077_, v___y_1943_);
if (v___x_2078_ == 0)
{
lean_dec(v___y_1965_);
lean_dec(v___y_1950_);
lean_dec(v___y_1943_);
v_a_1910_ = v___x_2076_;
v_a_1911_ = v_a_2015_;
goto v___jp_1909_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_of_nat(v___y_1943_);
lean_dec(v___y_1943_);
lean_inc(v_vis_x3f_1901_);
lean_inc(v_type_1924_);
lean_inc(v_structTy_1899_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1899_, v_type_1924_, v___y_1950_, v___y_1965_, v_vis_x3f_1901_, v_structId_1902_, v_ids_1923_, v___x_2079_, v___x_2080_, v___x_2076_, v___y_1907_, v_a_2015_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v_a_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
v_a_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2081_, 2);
v_a_1910_ = v_a_2082_;
v_a_1911_ = v_a_2083_;
goto v___jp_1909_;
}
else
{
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
return v___x_2081_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v___x_2010_);
lean_dec(v___x_2006_);
lean_dec_ref_known(v___x_1998_, 2);
lean_dec(v___x_1997_);
lean_dec(v___x_1995_);
lean_dec(v___x_1978_);
lean_dec_ref_known(v___x_1976_, 2);
lean_dec(v___x_1975_);
lean_dec(v___x_1972_);
lean_dec(v___x_1970_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v___y_1956_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec(v___y_1946_);
lean_dec(v___y_1943_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1933_);
lean_del_object(v___x_1919_);
lean_dec(v_fields_1917_);
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v_a_2085_ = lean_ctor_get(v___x_2013_, 0);
v_a_2086_ = lean_ctor_get(v___x_2013_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2013_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_inc(v_a_2085_);
lean_dec(v___x_2013_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2085_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
v___jp_2094_:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1915_, v___y_2099_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_n(v_a_2134_, 2);
v_a_2135_ = lean_ctor_get(v___x_2133_, 1);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2133_, 2);
v___x_2136_ = l_Lean_mkIdentFrom(v___y_2107_, v___y_2132_, v___x_1915_);
lean_dec(v___y_2107_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2100_);
v___x_2137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2137_, 0, v_a_2134_);
lean_ctor_set(v___x_2137_, 1, v___y_2100_);
lean_ctor_set(v___x_2137_, 2, v___y_2125_);
if (lean_obj_tag(v_vis_x3f_1901_) == 1)
{
lean_object* v_val_2138_; lean_object* v___x_2139_; 
v_val_2138_ = lean_ctor_get(v_vis_x3f_1901_, 0);
lean_inc(v_val_2138_);
v___x_2139_ = l_Array_mkArray1___redArg(v_val_2138_);
v___y_1928_ = v___y_2095_;
v___y_1929_ = v___y_2096_;
v___y_1930_ = v___y_2097_;
v___y_1931_ = v_a_2135_;
v___y_1932_ = v___y_2098_;
v___y_1933_ = v_a_2134_;
v___y_1934_ = v___y_2099_;
v___y_1935_ = v___y_2100_;
v___y_1936_ = v___y_2102_;
v___y_1937_ = v___y_2101_;
v___y_1938_ = v___y_2104_;
v___y_1939_ = v___y_2103_;
v___y_1940_ = v___y_2105_;
v___y_1941_ = v___y_2106_;
v___y_1942_ = v___x_2136_;
v___y_1943_ = v___y_2108_;
v___y_1944_ = v___y_2109_;
v___y_1945_ = v___y_2110_;
v___y_1946_ = v___y_2111_;
v___y_1947_ = v___y_2112_;
v___y_1948_ = v___y_2113_;
v___y_1949_ = v___y_2114_;
v___y_1950_ = v___y_2115_;
v___y_1951_ = v___y_2116_;
v___y_1952_ = v___y_2117_;
v___y_1953_ = v___y_2118_;
v___y_1954_ = v___y_2119_;
v___y_1955_ = v___y_2122_;
v___y_1956_ = v___y_2121_;
v___y_1957_ = v___y_2120_;
v___y_1958_ = v___y_2123_;
v___y_1959_ = v___y_2124_;
v___y_1960_ = v___y_2125_;
v___y_1961_ = v___y_2126_;
v___y_1962_ = v___x_2137_;
v___y_1963_ = v___y_2128_;
v___y_1964_ = v___y_2129_;
v___y_1965_ = v___y_2131_;
v___y_1966_ = v___y_2130_;
v___y_1967_ = v___x_2139_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_mk_empty_array_with_capacity(v___y_2127_);
v___y_1928_ = v___y_2095_;
v___y_1929_ = v___y_2096_;
v___y_1930_ = v___y_2097_;
v___y_1931_ = v_a_2135_;
v___y_1932_ = v___y_2098_;
v___y_1933_ = v_a_2134_;
v___y_1934_ = v___y_2099_;
v___y_1935_ = v___y_2100_;
v___y_1936_ = v___y_2102_;
v___y_1937_ = v___y_2101_;
v___y_1938_ = v___y_2104_;
v___y_1939_ = v___y_2103_;
v___y_1940_ = v___y_2105_;
v___y_1941_ = v___y_2106_;
v___y_1942_ = v___x_2136_;
v___y_1943_ = v___y_2108_;
v___y_1944_ = v___y_2109_;
v___y_1945_ = v___y_2110_;
v___y_1946_ = v___y_2111_;
v___y_1947_ = v___y_2112_;
v___y_1948_ = v___y_2113_;
v___y_1949_ = v___y_2114_;
v___y_1950_ = v___y_2115_;
v___y_1951_ = v___y_2116_;
v___y_1952_ = v___y_2117_;
v___y_1953_ = v___y_2118_;
v___y_1954_ = v___y_2119_;
v___y_1955_ = v___y_2122_;
v___y_1956_ = v___y_2121_;
v___y_1957_ = v___y_2120_;
v___y_1958_ = v___y_2123_;
v___y_1959_ = v___y_2124_;
v___y_1960_ = v___y_2125_;
v___y_1961_ = v___y_2126_;
v___y_1962_ = v___x_2137_;
v___y_1963_ = v___y_2128_;
v___y_1964_ = v___y_2129_;
v___y_1965_ = v___y_2131_;
v___y_1966_ = v___y_2130_;
v___y_1967_ = v___x_2140_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_a_2141_; lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v___y_2128_);
lean_dec(v___y_2126_);
lean_dec(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_del_object(v___x_1919_);
lean_dec(v_fields_1917_);
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v_a_2141_ = lean_ctor_get(v___x_2133_, 0);
v_a_2142_ = lean_ctor_get(v___x_2133_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2133_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_inc(v_a_2141_);
lean_dec(v___x_2133_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2141_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2150_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_ref_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_inc_ref(v___y_2182_);
v___x_2189_ = l_Array_append___redArg(v___y_2182_, v___y_2188_);
lean_dec_ref(v___y_2188_);
lean_inc_n(v___y_2157_, 4);
lean_inc_n(v___y_2179_, 18);
v___x_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___y_2179_);
lean_ctor_set(v___x_2190_, 1, v___y_2157_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_inc_n(v___y_2152_, 11);
lean_inc(v___y_2160_);
v___x_2191_ = l_Lean_Syntax_node7(v___y_2179_, v___y_2160_, v___y_2152_, v___y_2152_, v___x_2190_, v___y_2152_, v___y_2152_, v___y_2152_, v___y_2152_);
v___x_2192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_2159_, 3);
lean_inc_ref_n(v___y_2155_, 6);
lean_inc_ref_n(v___y_2168_, 6);
v___x_2193_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2159_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_2162_, 2);
v___x_2195_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2162_, v___x_2194_);
v___x_2196_ = l_Lean_Syntax_node1(v___y_2179_, v___x_2195_, v___y_2152_);
v___x_2197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2179_);
lean_ctor_set(v___x_2197_, 1, v___x_2192_);
v___x_2198_ = l_Lean_Syntax_node2(v___y_2179_, v___y_2176_, v___y_2175_, v___y_2152_);
v___x_2199_ = l_Lean_Syntax_node1(v___y_2179_, v___y_2157_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_2201_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2159_, v___x_2200_);
lean_inc_ref(v___y_2181_);
v___x_2202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___y_2179_);
lean_ctor_set(v___x_2202_, 1, v___y_2181_);
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_2204_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_2161_, 2);
lean_inc_n(v___y_2158_, 2);
v___x_2206_ = l_Lean_addMacroScope(v___y_2158_, v___x_2205_, v___y_2161_);
lean_inc_ref(v___y_2164_);
v___x_2207_ = l_Lean_Name_mkStr2(v___y_2164_, v___x_2203_);
lean_inc(v___y_2169_);
lean_inc(v___x_2207_);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___y_2169_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_inc(v___y_2167_);
v___x_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___y_2167_);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2208_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2179_);
lean_ctor_set(v___x_2212_, 1, v___x_2204_);
lean_ctor_set(v___x_2212_, 2, v___x_2206_);
lean_ctor_set(v___x_2212_, 3, v___x_2211_);
lean_inc(v_type_1924_);
lean_inc(v_structTy_1899_);
v___x_2213_ = l_Lean_Syntax_node2(v___y_2179_, v___y_2157_, v_structTy_1899_, v_type_1924_);
lean_inc(v___y_2180_);
v___x_2214_ = l_Lean_Syntax_node2(v___y_2179_, v___y_2180_, v___x_2212_, v___x_2213_);
v___x_2215_ = l_Lean_Syntax_node2(v___y_2179_, v___y_2165_, v___x_2202_, v___x_2214_);
v___x_2216_ = l_Lean_Syntax_node2(v___y_2179_, v___x_2201_, v___y_2152_, v___x_2215_);
v___x_2217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_2218_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2159_, v___x_2217_);
lean_inc_ref(v___y_2177_);
v___x_2219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2179_);
lean_ctor_set(v___x_2219_, 1, v___y_2177_);
v___x_2220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2221_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2162_, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___y_2179_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = l_Lean_Syntax_node1(v___y_2179_, v___y_2157_, v___y_2170_);
v___x_2225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___y_2179_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_Syntax_node3(v___y_2179_, v___x_2221_, v___x_2223_, v___x_2224_, v___x_2226_);
v___x_2228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2230_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___x_2228_, v___x_2229_);
v___x_2231_ = l_Lean_Syntax_node2(v___y_2179_, v___x_2230_, v___y_2152_, v___y_2152_);
v_ref_2232_ = l_Lean_replaceRef(v_fields_1917_, v___y_2156_);
lean_inc(v_ref_2232_);
lean_inc(v___y_2154_);
lean_inc(v___y_2153_);
lean_inc(v___y_2185_);
v___x_2233_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2185_);
lean_ctor_set(v___x_2233_, 1, v___y_2158_);
lean_ctor_set(v___x_2233_, 2, v___y_2161_);
lean_ctor_set(v___x_2233_, 3, v___y_2153_);
lean_ctor_set(v___x_2233_, 4, v___y_2154_);
lean_ctor_set(v___x_2233_, 5, v_ref_2232_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1915_, v_ref_2232_, v___x_2233_, v___y_2178_);
lean_dec_ref_known(v___x_2233_, 6);
lean_dec(v_ref_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_ref_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_n(v_a_2235_, 14);
v_a_2236_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2234_, 2);
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_2162_, 2);
lean_inc_ref_n(v___y_2155_, 5);
lean_inc_ref_n(v___y_2168_, 7);
v___x_2238_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2162_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2235_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_2161_, 4);
lean_inc_n(v___y_2158_, 4);
v___x_2243_ = l_Lean_addMacroScope(v___y_2158_, v___x_2242_, v___y_2161_);
lean_inc_n(v___y_2167_, 3);
v___x_2244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2244_, 0, v_a_2235_);
lean_ctor_set(v___x_2244_, 1, v___x_2241_);
lean_ctor_set(v___x_2244_, 2, v___x_2243_);
lean_ctor_set(v___x_2244_, 3, v___y_2167_);
lean_inc_ref(v___y_2182_);
lean_inc_n(v___y_2157_, 3);
v___x_2245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2245_, 0, v_a_2235_);
lean_ctor_set(v___x_2245_, 1, v___y_2157_);
lean_ctor_set(v___x_2245_, 2, v___y_2182_);
v___x_2246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_2247_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2162_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_2249_ = l_Lean_Name_mkStr4(v___y_2168_, v___y_2155_, v___y_2162_, v___x_2248_);
v___x_2250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_a_2235_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_2253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Lean_addMacroScope(v___y_2158_, v___x_2254_, v___y_2161_);
lean_inc_ref_n(v___y_2164_, 2);
v___x_2256_ = l_Lean_Name_mkStr1(v___y_2164_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_inc_ref(v___y_2159_);
v___x_2258_ = l_Lean_Name_mkStr3(v___y_2168_, v___y_2155_, v___y_2159_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
v___x_2260_ = l_Lean_Name_mkStr2(v___y_2168_, v___y_2155_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_2263_ = l_Lean_Name_mkStr2(v___y_2168_, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
v___x_2265_ = l_Lean_Name_mkStr1(v___y_2168_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___y_2167_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2264_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2261_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2259_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2257_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2235_);
lean_ctor_set(v___x_2272_, 1, v___x_2253_);
lean_ctor_set(v___x_2272_, 2, v___x_2255_);
lean_ctor_set(v___x_2272_, 3, v___x_2271_);
v___x_2273_ = l_Lean_Syntax_node1(v_a_2235_, v___x_2252_, v___x_2272_);
v___x_2274_ = l_Lean_Syntax_node2(v_a_2235_, v___x_2249_, v___x_2251_, v___x_2273_);
v___x_2275_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_2279_ = l_Lean_addMacroScope(v___y_2158_, v___x_2278_, v___y_2161_);
v___x_2280_ = l_Lean_Name_mkStr3(v___y_2164_, v___x_2276_, v___x_2277_);
lean_inc(v___y_2169_);
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___y_2169_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___y_2167_);
v___x_2283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2235_);
lean_ctor_set(v___x_2283_, 1, v___x_2275_);
lean_ctor_set(v___x_2283_, 2, v___x_2279_);
lean_ctor_set(v___x_2283_, 3, v___x_2282_);
lean_inc(v_type_1924_);
v___x_2284_ = l_Lean_Syntax_node1(v_a_2235_, v___y_2157_, v_type_1924_);
v___x_2285_ = l_Lean_Syntax_node2(v_a_2235_, v___y_2180_, v___x_2283_, v___x_2284_);
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_2287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_a_2235_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_Syntax_node3(v_a_2235_, v___x_2247_, v___x_2274_, v___x_2285_, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node1(v_a_2235_, v___y_2157_, v___x_2288_);
lean_inc(v___x_2238_);
v___x_2290_ = l_Lean_Syntax_node5(v_a_2235_, v___x_2238_, v_fields_1917_, v___x_2240_, v___x_2244_, v___x_2245_, v___x_2289_);
v_ref_2291_ = l_Lean_replaceRef(v___x_2290_, v___y_2156_);
lean_inc(v_ref_2291_);
lean_inc(v___y_2154_);
lean_inc(v___y_2153_);
lean_inc(v___y_2185_);
v___x_2292_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2292_, 0, v___y_2185_);
lean_ctor_set(v___x_2292_, 1, v___y_2158_);
lean_ctor_set(v___x_2292_, 2, v___y_2161_);
lean_ctor_set(v___x_2292_, 3, v___y_2153_);
lean_ctor_set(v___x_2292_, 4, v___y_2154_);
lean_ctor_set(v___x_2292_, 5, v_ref_2291_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1915_, v_ref_2291_, v___x_2292_, v_a_2236_);
lean_dec_ref_known(v___x_2292_, 6);
lean_dec(v_ref_2291_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_n(v_a_2294_, 29);
v_a_2295_ = lean_ctor_get(v___x_2293_, 1);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2293_, 2);
lean_inc(v___y_2152_);
lean_inc_n(v___y_2179_, 2);
v___x_2296_ = l_Lean_Syntax_node4(v___y_2179_, v___x_2218_, v___x_2219_, v___x_2227_, v___x_2231_, v___y_2152_);
v___x_2297_ = l_Lean_Syntax_node6(v___y_2179_, v___x_2193_, v___x_2196_, v___x_2197_, v___y_2152_, v___x_2199_, v___x_2216_, v___x_2296_);
lean_inc(v___y_2172_);
v___x_2298_ = l_Lean_Syntax_node2(v___y_2179_, v___y_2172_, v___x_2191_, v___x_2297_);
v___x_2299_ = lean_array_push(v___y_2171_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_a_2294_);
lean_ctor_set(v___x_2300_, 1, v___x_2239_);
v___x_2301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_2161_, 6);
lean_inc_n(v___y_2158_, 6);
v___x_2303_ = l_Lean_addMacroScope(v___y_2158_, v___x_2302_, v___y_2161_);
lean_inc_n(v___y_2167_, 6);
v___x_2304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2294_);
lean_ctor_set(v___x_2304_, 1, v___x_2301_);
lean_ctor_set(v___x_2304_, 2, v___x_2303_);
lean_ctor_set(v___x_2304_, 3, v___y_2167_);
lean_inc_ref(v___y_2182_);
lean_inc_n(v___y_2157_, 6);
v___x_2305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2294_);
lean_ctor_set(v___x_2305_, 1, v___y_2157_);
lean_ctor_set(v___x_2305_, 2, v___y_2182_);
lean_inc_ref(v___y_2174_);
v___x_2306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_a_2294_);
lean_ctor_set(v___x_2306_, 1, v___y_2174_);
v___x_2307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2309_ = l_Lean_addMacroScope(v___y_2158_, v___x_2308_, v___y_2161_);
v___x_2310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2310_, 0, v_a_2294_);
lean_ctor_set(v___x_2310_, 1, v___x_2307_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
lean_ctor_set(v___x_2310_, 3, v___y_2167_);
lean_inc_ref_n(v___x_2305_, 14);
lean_inc_n(v___y_2163_, 2);
v___x_2311_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2163_, v___x_2310_, v___x_2305_);
lean_inc_ref(v___y_2177_);
v___x_2312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_a_2294_);
lean_ctor_set(v___x_2312_, 1, v___y_2177_);
lean_inc_ref(v___x_2312_);
lean_inc(v___y_2187_);
v___x_2313_ = l_Lean_Syntax_node3(v_a_2294_, v___y_2187_, v___x_2312_, v___x_2305_, v___y_2186_);
v___x_2314_ = l_Lean_Syntax_node3(v_a_2294_, v___y_2157_, v___x_2305_, v___x_2305_, v___x_2313_);
lean_inc(v___x_2314_);
lean_inc_n(v___y_2183_, 2);
v___x_2315_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2183_, v___x_2311_, v___x_2314_);
v___x_2316_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2318_ = l_Lean_addMacroScope(v___y_2158_, v___x_2317_, v___y_2161_);
v___x_2319_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2319_, 0, v_a_2294_);
lean_ctor_set(v___x_2319_, 1, v___x_2316_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
lean_ctor_set(v___x_2319_, 3, v___y_2167_);
v___x_2320_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2163_, v___x_2319_, v___x_2305_);
v___x_2321_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2183_, v___x_2320_, v___x_2314_);
v___x_2322_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_2323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_2324_ = l_Lean_addMacroScope(v___y_2158_, v___x_2323_, v___y_2161_);
v___x_2325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2325_, 0, v_a_2294_);
lean_ctor_set(v___x_2325_, 1, v___x_2322_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
lean_ctor_set(v___x_2325_, 3, v___y_2167_);
v___x_2326_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2163_, v___x_2325_, v___x_2305_);
v___x_2327_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_2328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_2329_ = l_Lean_addMacroScope(v___y_2158_, v___x_2328_, v___y_2161_);
v___x_2330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_2169_, 2);
v___x_2331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___y_2169_);
v___x_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___y_2167_);
v___x_2333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2294_);
lean_ctor_set(v___x_2333_, 1, v___x_2327_);
lean_ctor_set(v___x_2333_, 2, v___x_2329_);
lean_ctor_set(v___x_2333_, 3, v___x_2332_);
v___x_2334_ = l_Lean_Syntax_node3(v_a_2294_, v___y_2187_, v___x_2312_, v___x_2305_, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node3(v_a_2294_, v___y_2157_, v___x_2305_, v___x_2305_, v___x_2334_);
v___x_2336_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2183_, v___x_2326_, v___x_2335_);
v___x_2337_ = l_Lean_Syntax_node6(v_a_2294_, v___y_2157_, v___x_2315_, v___x_2305_, v___x_2321_, v___x_2305_, v___x_2336_, v___x_2305_);
v___x_2338_ = l_Lean_Syntax_node1(v_a_2294_, v___y_2173_, v___x_2337_);
v___x_2339_ = l_Lean_Syntax_node1(v_a_2294_, v___y_2166_, v___x_2305_);
lean_inc_ref(v___y_2181_);
v___x_2340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_a_2294_);
lean_ctor_set(v___x_2340_, 1, v___y_2181_);
v___x_2341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2344_ = l_Lean_addMacroScope(v___y_2158_, v___x_2343_, v___y_2161_);
lean_inc_ref(v___y_2164_);
v___x_2345_ = l_Lean_Name_mkStr2(v___y_2164_, v___x_2341_);
lean_inc(v___x_2345_);
v___x_2346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___y_2169_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___y_2167_);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2294_);
lean_ctor_set(v___x_2350_, 1, v___x_2342_);
lean_ctor_set(v___x_2350_, 2, v___x_2344_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
v___x_2351_ = l_Lean_Syntax_node2(v_a_2294_, v___y_2157_, v___x_2340_, v___x_2350_);
lean_inc_ref(v___y_2151_);
v___x_2352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2294_);
lean_ctor_set(v___x_2352_, 1, v___y_2151_);
v___x_2353_ = l_Lean_Syntax_node6(v_a_2294_, v___y_2184_, v___x_2306_, v___x_2305_, v___x_2338_, v___x_2339_, v___x_2351_, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node1(v_a_2294_, v___y_2157_, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_node5(v_a_2294_, v___x_2238_, v___x_2290_, v___x_2300_, v___x_2304_, v___x_2305_, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2299_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v_a_1910_ = v___x_2356_;
v_a_1911_ = v_a_2295_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v___x_2290_);
lean_dec(v___x_2238_);
lean_dec(v___x_2231_);
lean_dec(v___x_2227_);
lean_dec_ref_known(v___x_2219_, 2);
lean_dec(v___x_2218_);
lean_dec(v___x_2216_);
lean_dec(v___x_2199_);
lean_dec_ref_known(v___x_2197_, 2);
lean_dec(v___x_2196_);
lean_dec(v___x_2193_);
lean_dec(v___x_2191_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec(v___y_2179_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2166_);
lean_dec(v___y_2163_);
lean_dec(v___y_2152_);
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v_a_2357_ = lean_ctor_get(v___x_2293_, 0);
v_a_2358_ = lean_ctor_get(v___x_2293_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2293_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_inc(v_a_2357_);
lean_dec(v___x_2293_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2357_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v___x_2231_);
lean_dec(v___x_2227_);
lean_dec_ref_known(v___x_2219_, 2);
lean_dec(v___x_2218_);
lean_dec(v___x_2216_);
lean_dec(v___x_2199_);
lean_dec_ref_known(v___x_2197_, 2);
lean_dec(v___x_2196_);
lean_dec(v___x_2193_);
lean_dec(v___x_2191_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2166_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2152_);
lean_dec(v_fields_1917_);
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v_a_2366_ = lean_ctor_get(v___x_2234_, 0);
v_a_2367_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2234_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_inc(v_a_2366_);
lean_dec(v___x_2234_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2366_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
v___jp_2375_:
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1915_, v___y_2380_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_n(v_a_2411_, 2);
v_a_2412_ = lean_ctor_get(v___x_2410_, 1);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2410_, 2);
v___x_2413_ = l_Lean_mkIdentFrom(v_id_1922_, v___y_2409_, v___x_1915_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2381_);
v___x_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2414_, 0, v_a_2411_);
lean_ctor_set(v___x_2414_, 1, v___y_2381_);
lean_ctor_set(v___x_2414_, 2, v___y_2403_);
if (lean_obj_tag(v_vis_x3f_1901_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2416_; 
v_val_2415_ = lean_ctor_get(v_vis_x3f_1901_, 0);
lean_inc(v_val_2415_);
v___x_2416_ = l_Array_mkArray1___redArg(v_val_2415_);
v___y_2151_ = v___y_2376_;
v___y_2152_ = v___x_2414_;
v___y_2153_ = v___y_2377_;
v___y_2154_ = v___y_2378_;
v___y_2155_ = v___y_2379_;
v___y_2156_ = v___y_2380_;
v___y_2157_ = v___y_2381_;
v___y_2158_ = v___y_2383_;
v___y_2159_ = v___y_2382_;
v___y_2160_ = v___y_2385_;
v___y_2161_ = v___y_2384_;
v___y_2162_ = v___y_2386_;
v___y_2163_ = v___y_2387_;
v___y_2164_ = v___y_2388_;
v___y_2165_ = v___y_2389_;
v___y_2166_ = v___y_2390_;
v___y_2167_ = v___y_2391_;
v___y_2168_ = v___y_2392_;
v___y_2169_ = v___y_2393_;
v___y_2170_ = v___y_2394_;
v___y_2171_ = v___y_2395_;
v___y_2172_ = v___y_2396_;
v___y_2173_ = v___y_2397_;
v___y_2174_ = v___y_2398_;
v___y_2175_ = v___x_2413_;
v___y_2176_ = v___y_2400_;
v___y_2177_ = v___y_2399_;
v___y_2178_ = v_a_2412_;
v___y_2179_ = v_a_2411_;
v___y_2180_ = v___y_2401_;
v___y_2181_ = v___y_2402_;
v___y_2182_ = v___y_2403_;
v___y_2183_ = v___y_2404_;
v___y_2184_ = v___y_2405_;
v___y_2185_ = v___y_2406_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v___y_2407_;
v___y_2188_ = v___x_2416_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2151_ = v___y_2376_;
v___y_2152_ = v___x_2414_;
v___y_2153_ = v___y_2377_;
v___y_2154_ = v___y_2378_;
v___y_2155_ = v___y_2379_;
v___y_2156_ = v___y_2380_;
v___y_2157_ = v___y_2381_;
v___y_2158_ = v___y_2383_;
v___y_2159_ = v___y_2382_;
v___y_2160_ = v___y_2385_;
v___y_2161_ = v___y_2384_;
v___y_2162_ = v___y_2386_;
v___y_2163_ = v___y_2387_;
v___y_2164_ = v___y_2388_;
v___y_2165_ = v___y_2389_;
v___y_2166_ = v___y_2390_;
v___y_2167_ = v___y_2391_;
v___y_2168_ = v___y_2392_;
v___y_2169_ = v___y_2393_;
v___y_2170_ = v___y_2394_;
v___y_2171_ = v___y_2395_;
v___y_2172_ = v___y_2396_;
v___y_2173_ = v___y_2397_;
v___y_2174_ = v___y_2398_;
v___y_2175_ = v___x_2413_;
v___y_2176_ = v___y_2400_;
v___y_2177_ = v___y_2399_;
v___y_2178_ = v_a_2412_;
v___y_2179_ = v_a_2411_;
v___y_2180_ = v___y_2401_;
v___y_2181_ = v___y_2402_;
v___y_2182_ = v___y_2403_;
v___y_2183_ = v___y_2404_;
v___y_2184_ = v___y_2405_;
v___y_2185_ = v___y_2406_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v___y_2407_;
v___y_2188_ = v___x_2417_;
goto v___jp_2150_;
}
}
else
{
lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v_fields_1917_);
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v_a_2418_ = lean_ctor_get(v___x_2410_, 0);
v_a_2419_ = lean_ctor_get(v___x_2410_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2410_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_inc(v_a_2418_);
lean_dec(v___x_2410_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2418_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
v___jp_2428_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_inc_ref_n(v___y_2442_, 2);
v___x_2446_ = l_Array_append___redArg(v___y_2442_, v___y_2445_);
lean_dec_ref(v___y_2445_);
lean_inc_n(v___y_2436_, 19);
lean_inc_n(v___y_2429_, 69);
v___x_2447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2447_, 0, v___y_2429_);
lean_ctor_set(v___x_2447_, 1, v___y_2436_);
lean_ctor_set(v___x_2447_, 2, v___x_2446_);
lean_inc_n(v___y_2444_, 35);
lean_inc(v___y_2440_);
v___x_2448_ = l_Lean_Syntax_node7(v___y_2429_, v___y_2440_, v___y_2444_, v___y_2444_, v___x_2447_, v___y_2444_, v___y_2444_, v___y_2444_, v___y_2444_);
v___x_2449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_2438_, 4);
lean_inc_ref_n(v___y_2433_, 15);
lean_inc_ref_n(v___y_2432_, 15);
v___x_2450_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___y_2438_, v___x_2449_);
v___x_2451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2429_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_2454_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___y_2438_, v___x_2453_);
lean_inc(v___y_2434_);
lean_inc(v___x_2454_);
v___x_2455_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2454_, v___y_2434_, v___y_2444_);
v___x_2456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_2457_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___y_2438_, v___x_2456_);
v___x_2458_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_2459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_2460_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2429_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_2464_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2463_);
v___x_2465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_2441_, 8);
lean_inc_n(v___y_2439_, 8);
v___x_2467_ = l_Lean_addMacroScope(v___y_2439_, v___x_2466_, v___y_2441_);
v___x_2468_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_2469_ = lean_box(0);
v___x_2470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_2471_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2471_, 0, v___y_2429_);
lean_ctor_set(v___x_2471_, 1, v___x_2465_);
lean_ctor_set(v___x_2471_, 2, v___x_2467_);
lean_ctor_set(v___x_2471_, 3, v___x_2470_);
lean_inc(v_type_1924_);
lean_inc(v_structTy_1899_);
v___x_2472_ = l_Lean_Syntax_node2(v___y_2429_, v___y_2436_, v_structTy_1899_, v_type_1924_);
lean_inc_n(v___x_2464_, 2);
v___x_2473_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2464_, v___x_2471_, v___x_2472_);
lean_inc(v___x_2460_);
v___x_2474_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2460_, v___x_2462_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_2474_);
v___x_2476_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2457_, v___y_2444_, v___x_2475_);
v___x_2477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_2478_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___y_2438_, v___x_2477_);
v___x_2479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_2480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2429_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_2482_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2481_);
v___x_2483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_2484_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_2486_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2485_);
v___x_2487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_2488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_2489_ = l_Lean_addMacroScope(v___y_2439_, v___x_2488_, v___y_2441_);
v___x_2490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_2491_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2491_, 0, v___y_2429_);
lean_ctor_set(v___x_2491_, 1, v___x_2487_);
lean_ctor_set(v___x_2491_, 2, v___x_2489_);
lean_ctor_set(v___x_2491_, 3, v___x_2490_);
lean_inc_n(v___x_2486_, 5);
v___x_2492_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2486_, v___x_2491_, v___y_2444_);
v___x_2493_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_2494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_2495_ = l_Lean_addMacroScope(v___y_2439_, v___x_2494_, v___y_2441_);
v___x_2496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2429_);
lean_ctor_set(v___x_2496_, 1, v___x_2493_);
lean_ctor_set(v___x_2496_, 2, v___x_2495_);
lean_ctor_set(v___x_2496_, 3, v___x_2469_);
lean_inc_ref_n(v___x_2496_, 3);
v___x_2497_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_2496_);
v___x_2498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_2499_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2498_);
v___x_2500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___y_2429_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_2503_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2502_);
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_2505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___y_2429_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
lean_inc_n(v_id_1922_, 3);
v___x_2506_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2503_, v___x_2496_, v___x_2505_, v_id_1922_);
lean_inc(v___x_2506_);
lean_inc_ref_n(v___x_2501_, 5);
lean_inc_n(v___x_2499_, 6);
v___x_2507_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2506_);
lean_inc(v___x_2497_);
v___x_2508_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___x_2497_, v___y_2444_, v___x_2507_);
lean_inc_n(v___x_2484_, 6);
v___x_2509_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2492_, v___x_2508_);
v___x_2510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_2512_ = l_Lean_addMacroScope(v___y_2439_, v___x_2511_, v___y_2441_);
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_2514_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2429_);
lean_ctor_set(v___x_2514_, 1, v___x_2510_);
lean_ctor_set(v___x_2514_, 2, v___x_2512_);
lean_ctor_set(v___x_2514_, 3, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2486_, v___x_2514_, v___y_2444_);
v___x_2516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_2517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_2518_ = l_Lean_addMacroScope(v___y_2439_, v___x_2517_, v___y_2441_);
v___x_2519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2519_, 0, v___y_2429_);
lean_ctor_set(v___x_2519_, 1, v___x_2516_);
lean_ctor_set(v___x_2519_, 2, v___x_2518_);
lean_ctor_set(v___x_2519_, 3, v___x_2469_);
lean_inc_ref(v___x_2519_);
v___x_2520_ = l_Lean_Syntax_node2(v___y_2429_, v___y_2436_, v___x_2519_, v___x_2496_);
v___x_2521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_2522_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2521_);
v___x_2523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_2524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___y_2429_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___y_2429_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = l_Lean_Syntax_node2(v___y_2429_, v___y_2436_, v___x_2497_, v___x_2526_);
v___x_2528_ = lean_box(0);
v___x_2529_ = l_Lean_SourceInfo_fromRef(v___x_2528_, v___x_1915_);
lean_inc(v___x_2529_);
v___x_2530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___y_2436_);
lean_ctor_set(v___x_2530_, 2, v___y_2442_);
v___x_2531_ = l_Lean_Syntax_node2(v___x_2529_, v___x_2486_, v_id_1922_, v___x_2530_);
v___x_2532_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2519_);
v___x_2533_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___y_2444_, v___y_2444_, v___x_2532_);
lean_inc(v___x_2531_);
v___x_2534_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2531_, v___x_2533_);
v___x_2535_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_2534_);
lean_inc_n(v___x_2482_, 3);
v___x_2536_ = l_Lean_Syntax_node1(v___y_2429_, v___x_2482_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_2538_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2537_);
lean_inc(v___x_2538_);
v___x_2539_ = l_Lean_Syntax_node1(v___y_2429_, v___x_2538_, v___y_2444_);
v___x_2540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___y_2429_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_inc_ref(v___x_2541_);
lean_inc(v___x_2539_);
lean_inc(v___x_2527_);
lean_inc_ref(v___x_2524_);
lean_inc_n(v___x_2522_, 2);
v___x_2542_ = l_Lean_Syntax_node6(v___y_2429_, v___x_2522_, v___x_2524_, v___x_2527_, v___x_2536_, v___x_2539_, v___y_2444_, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2542_);
v___x_2544_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___x_2520_, v___y_2444_, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2515_, v___x_2544_);
v___x_2546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_2547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_2548_ = l_Lean_addMacroScope(v___y_2439_, v___x_2547_, v___y_2441_);
v___x_2549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_2550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2550_, 0, v___y_2429_);
lean_ctor_set(v___x_2550_, 1, v___x_2546_);
lean_ctor_set(v___x_2550_, 2, v___x_2548_);
lean_ctor_set(v___x_2550_, 3, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2486_, v___x_2550_, v___y_2444_);
v___x_2552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_2553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_2554_ = l_Lean_addMacroScope(v___y_2439_, v___x_2553_, v___y_2441_);
v___x_2555_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2429_);
lean_ctor_set(v___x_2555_, 1, v___x_2552_);
lean_ctor_set(v___x_2555_, 2, v___x_2554_);
lean_ctor_set(v___x_2555_, 3, v___x_2469_);
lean_inc_ref(v___x_2555_);
v___x_2556_ = l_Lean_Syntax_node2(v___y_2429_, v___y_2436_, v___x_2555_, v___x_2496_);
v___x_2557_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_2506_);
v___x_2558_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2464_, v___x_2555_, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___y_2444_, v___y_2444_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2531_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_2561_);
v___x_2563_ = l_Lean_Syntax_node1(v___y_2429_, v___x_2482_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node6(v___y_2429_, v___x_2522_, v___x_2524_, v___x_2527_, v___x_2563_, v___x_2539_, v___y_2444_, v___x_2541_);
v___x_2565_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___x_2556_, v___y_2444_, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2551_, v___x_2566_);
v___x_2568_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_2569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_2570_ = l_Lean_addMacroScope(v___y_2439_, v___x_2569_, v___y_2441_);
v___x_2571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2429_);
lean_ctor_set(v___x_2571_, 1, v___x_2568_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
lean_ctor_set(v___x_2571_, 3, v___x_2469_);
v___x_2572_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2486_, v___x_2571_, v___y_2444_);
v___x_2573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_2574_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2429_);
lean_ctor_set(v___x_2575_, 1, v___x_2573_);
v___x_2576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_2577_ = l_Lean_Name_mkStr4(v___y_2432_, v___y_2433_, v___x_2458_, v___x_2576_);
lean_inc(v___x_1900_);
v___x_2578_ = l_Lean_Syntax_node1(v___y_2429_, v___y_2436_, v___x_1900_);
v___x_2579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_2580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2429_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
lean_inc(v_defVal_1925_);
v___x_2581_ = l_Lean_Syntax_node4(v___y_2429_, v___x_2577_, v___x_2578_, v___y_2444_, v___x_2580_, v_defVal_1925_);
v___x_2582_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2574_, v___x_2575_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2499_, v___x_2501_, v___y_2444_, v___x_2582_);
v___x_2584_ = l_Lean_Syntax_node3(v___y_2429_, v___y_2436_, v___y_2444_, v___y_2444_, v___x_2583_);
v___x_2585_ = l_Lean_Syntax_node2(v___y_2429_, v___x_2484_, v___x_2572_, v___x_2584_);
v___x_2586_ = l_Lean_Syntax_node7(v___y_2429_, v___y_2436_, v___x_2509_, v___y_2444_, v___x_2545_, v___y_2444_, v___x_2567_, v___y_2444_, v___x_2585_);
v___x_2587_ = l_Lean_Syntax_node1(v___y_2429_, v___x_2482_, v___x_2586_);
v___x_2588_ = l_Lean_Syntax_node3(v___y_2429_, v___x_2478_, v___x_2480_, v___x_2587_, v___y_2444_);
v___x_2589_ = l_Lean_Syntax_node5(v___y_2429_, v___x_2450_, v___x_2452_, v___x_2455_, v___x_2476_, v___x_2588_, v___y_2444_);
lean_inc(v___y_2437_);
v___x_2590_ = l_Lean_Syntax_node2(v___y_2429_, v___y_2437_, v___x_2448_, v___x_2589_);
v___x_2591_ = lean_array_push(v_cmds_1916_, v___x_2590_);
lean_inc(v___x_2427_);
v___x_2592_ = l_Lake_Name_quoteFrom(v_id_1922_, v___x_2427_, v___x_1915_);
if (v_parent_1926_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
lean_dec(v___x_2427_);
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = lean_array_get_size(v_ids_1923_);
v___x_2595_ = lean_nat_dec_lt(v___x_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_dec(v___x_2592_);
lean_dec(v___x_2538_);
lean_dec(v___x_2522_);
lean_dec(v___x_2499_);
lean_dec(v___x_2486_);
lean_dec(v___x_2484_);
lean_dec(v___x_2482_);
lean_dec(v___x_2464_);
lean_dec(v___x_2460_);
lean_dec(v___x_2454_);
lean_dec(v___y_2434_);
lean_del_object(v___x_1919_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2591_);
lean_ctor_set(v___x_2596_, 1, v_fields_1917_);
v_a_1910_ = v___x_2596_;
v_a_1911_ = v___y_1908_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2597_ = lean_array_fget_borrowed(v_ids_1923_, v___x_2593_);
v___x_2598_ = l_Lean_TSyntax_getId(v___x_2597_);
lean_inc(v___x_2598_);
lean_inc(v___x_2597_);
v___x_2599_ = l_Lake_Name_quoteFrom(v___x_2597_, v___x_2598_, v___x_1915_);
v___x_2600_ = l_Lean_Name_hasMacroScopes(v___x_2598_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1902_, v___x_2598_);
lean_inc(v___x_2597_);
v___y_2095_ = v___x_2540_;
v___y_2096_ = v___y_2430_;
v___y_2097_ = v___y_2431_;
v___y_2098_ = v___y_2433_;
v___y_2099_ = v___y_2435_;
v___y_2100_ = v___y_2436_;
v___y_2101_ = v___y_2438_;
v___y_2102_ = v___y_2439_;
v___y_2103_ = v___y_2441_;
v___y_2104_ = v___y_2440_;
v___y_2105_ = v___x_2458_;
v___y_2106_ = v___x_2486_;
v___y_2107_ = v___x_2597_;
v___y_2108_ = v___x_2594_;
v___y_2109_ = v___x_2468_;
v___y_2110_ = v___x_2460_;
v___y_2111_ = v___x_2538_;
v___y_2112_ = v___x_2469_;
v___y_2113_ = v___y_2432_;
v___y_2114_ = v___x_2469_;
v___y_2115_ = v___y_2434_;
v___y_2116_ = v___x_2591_;
v___y_2117_ = v___y_2437_;
v___y_2118_ = v___x_2482_;
v___y_2119_ = v___x_2523_;
v___y_2120_ = v___x_2500_;
v___y_2121_ = v___x_2599_;
v___y_2122_ = v___x_2454_;
v___y_2123_ = v___x_2464_;
v___y_2124_ = v___x_2461_;
v___y_2125_ = v___y_2442_;
v___y_2126_ = v___x_2484_;
v___y_2127_ = v___x_2593_;
v___y_2128_ = v___x_2522_;
v___y_2129_ = v___y_2443_;
v___y_2130_ = v___x_2499_;
v___y_2131_ = v___x_2592_;
v___y_2132_ = v___x_2601_;
goto v___jp_2094_;
}
else
{
lean_object* v_view_2602_; lean_object* v_name_2603_; lean_object* v_imported_2604_; lean_object* v_ctx_2605_; lean_object* v_scopes_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2615_; 
v_view_2602_ = l_Lean_extractMacroScopes(v___x_2598_);
v_name_2603_ = lean_ctor_get(v_view_2602_, 0);
v_imported_2604_ = lean_ctor_get(v_view_2602_, 1);
v_ctx_2605_ = lean_ctor_get(v_view_2602_, 2);
v_scopes_2606_ = lean_ctor_get(v_view_2602_, 3);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_view_2602_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2608_ = v_view_2602_;
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_scopes_2606_);
lean_inc(v_ctx_2605_);
lean_inc(v_imported_2604_);
lean_inc(v_name_2603_);
lean_dec(v_view_2602_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1902_, v_name_2603_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_imported_2604_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_ctx_2605_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_scopes_2606_);
v___x_2612_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_MacroScopesView_review(v___x_2612_);
lean_inc(v___x_2597_);
v___y_2095_ = v___x_2540_;
v___y_2096_ = v___y_2430_;
v___y_2097_ = v___y_2431_;
v___y_2098_ = v___y_2433_;
v___y_2099_ = v___y_2435_;
v___y_2100_ = v___y_2436_;
v___y_2101_ = v___y_2438_;
v___y_2102_ = v___y_2439_;
v___y_2103_ = v___y_2441_;
v___y_2104_ = v___y_2440_;
v___y_2105_ = v___x_2458_;
v___y_2106_ = v___x_2486_;
v___y_2107_ = v___x_2597_;
v___y_2108_ = v___x_2594_;
v___y_2109_ = v___x_2468_;
v___y_2110_ = v___x_2460_;
v___y_2111_ = v___x_2538_;
v___y_2112_ = v___x_2469_;
v___y_2113_ = v___y_2432_;
v___y_2114_ = v___x_2469_;
v___y_2115_ = v___y_2434_;
v___y_2116_ = v___x_2591_;
v___y_2117_ = v___y_2437_;
v___y_2118_ = v___x_2482_;
v___y_2119_ = v___x_2523_;
v___y_2120_ = v___x_2500_;
v___y_2121_ = v___x_2599_;
v___y_2122_ = v___x_2454_;
v___y_2123_ = v___x_2464_;
v___y_2124_ = v___x_2461_;
v___y_2125_ = v___y_2442_;
v___y_2126_ = v___x_2484_;
v___y_2127_ = v___x_2593_;
v___y_2128_ = v___x_2522_;
v___y_2129_ = v___y_2443_;
v___y_2130_ = v___x_2499_;
v___y_2131_ = v___x_2592_;
v___y_2132_ = v___x_2613_;
goto v___jp_2094_;
}
}
}
}
}
else
{
uint8_t v___x_2616_; 
lean_del_object(v___x_1919_);
v___x_2616_ = l_Lean_Name_hasMacroScopes(v___x_2427_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1902_, v___x_2427_);
v___y_2376_ = v___x_2540_;
v___y_2377_ = v___y_2430_;
v___y_2378_ = v___y_2431_;
v___y_2379_ = v___y_2433_;
v___y_2380_ = v___y_2435_;
v___y_2381_ = v___y_2436_;
v___y_2382_ = v___y_2438_;
v___y_2383_ = v___y_2439_;
v___y_2384_ = v___y_2441_;
v___y_2385_ = v___y_2440_;
v___y_2386_ = v___x_2458_;
v___y_2387_ = v___x_2486_;
v___y_2388_ = v___x_2468_;
v___y_2389_ = v___x_2460_;
v___y_2390_ = v___x_2538_;
v___y_2391_ = v___x_2469_;
v___y_2392_ = v___y_2432_;
v___y_2393_ = v___x_2469_;
v___y_2394_ = v___y_2434_;
v___y_2395_ = v___x_2591_;
v___y_2396_ = v___y_2437_;
v___y_2397_ = v___x_2482_;
v___y_2398_ = v___x_2523_;
v___y_2399_ = v___x_2500_;
v___y_2400_ = v___x_2454_;
v___y_2401_ = v___x_2464_;
v___y_2402_ = v___x_2461_;
v___y_2403_ = v___y_2442_;
v___y_2404_ = v___x_2484_;
v___y_2405_ = v___x_2522_;
v___y_2406_ = v___y_2443_;
v___y_2407_ = v___x_2499_;
v___y_2408_ = v___x_2592_;
v___y_2409_ = v___x_2617_;
goto v___jp_2375_;
}
else
{
lean_object* v_view_2618_; lean_object* v_name_2619_; lean_object* v_imported_2620_; lean_object* v_ctx_2621_; lean_object* v_scopes_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2631_; 
v_view_2618_ = l_Lean_extractMacroScopes(v___x_2427_);
v_name_2619_ = lean_ctor_get(v_view_2618_, 0);
v_imported_2620_ = lean_ctor_get(v_view_2618_, 1);
v_ctx_2621_ = lean_ctor_get(v_view_2618_, 2);
v_scopes_2622_ = lean_ctor_get(v_view_2618_, 3);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_view_2618_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2624_ = v_view_2618_;
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_scopes_2622_);
lean_inc(v_ctx_2621_);
lean_inc(v_imported_2620_);
lean_inc(v_name_2619_);
lean_dec(v_view_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1902_, v_name_2619_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_imported_2620_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_ctx_2621_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_scopes_2622_);
v___x_2628_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_MacroScopesView_review(v___x_2628_);
v___y_2376_ = v___x_2540_;
v___y_2377_ = v___y_2430_;
v___y_2378_ = v___y_2431_;
v___y_2379_ = v___y_2433_;
v___y_2380_ = v___y_2435_;
v___y_2381_ = v___y_2436_;
v___y_2382_ = v___y_2438_;
v___y_2383_ = v___y_2439_;
v___y_2384_ = v___y_2441_;
v___y_2385_ = v___y_2440_;
v___y_2386_ = v___x_2458_;
v___y_2387_ = v___x_2486_;
v___y_2388_ = v___x_2468_;
v___y_2389_ = v___x_2460_;
v___y_2390_ = v___x_2538_;
v___y_2391_ = v___x_2469_;
v___y_2392_ = v___y_2432_;
v___y_2393_ = v___x_2469_;
v___y_2394_ = v___y_2434_;
v___y_2395_ = v___x_2591_;
v___y_2396_ = v___y_2437_;
v___y_2397_ = v___x_2482_;
v___y_2398_ = v___x_2523_;
v___y_2399_ = v___x_2500_;
v___y_2400_ = v___x_2454_;
v___y_2401_ = v___x_2464_;
v___y_2402_ = v___x_2461_;
v___y_2403_ = v___y_2442_;
v___y_2404_ = v___x_2484_;
v___y_2405_ = v___x_2522_;
v___y_2406_ = v___y_2443_;
v___y_2407_ = v___x_2499_;
v___y_2408_ = v___x_2592_;
v___y_2409_ = v___x_2629_;
goto v___jp_2375_;
}
}
}
}
}
v___jp_2632_:
{
lean_object* v_methods_2634_; lean_object* v_quotContext_2635_; lean_object* v_currMacroScope_2636_; lean_object* v_currRecDepth_2637_; lean_object* v_maxRecDepth_2638_; lean_object* v_ref_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_methods_2634_ = lean_ctor_get(v___y_1907_, 0);
v_quotContext_2635_ = lean_ctor_get(v___y_1907_, 1);
v_currMacroScope_2636_ = lean_ctor_get(v___y_1907_, 2);
v_currRecDepth_2637_ = lean_ctor_get(v___y_1907_, 3);
v_maxRecDepth_2638_ = lean_ctor_get(v___y_1907_, 4);
v_ref_2639_ = lean_ctor_get(v___y_1907_, 5);
v___x_2640_ = l_Lean_mkIdentFrom(v_id_1922_, v___y_2633_, v___x_1915_);
v___x_2641_ = l_Lean_SourceInfo_fromRef(v_ref_2639_, v___x_1915_);
v___x_2642_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2643_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2644_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_2646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_2647_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2648_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_2641_);
v___x_2649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2641_);
lean_ctor_set(v___x_2649_, 1, v___x_2647_);
lean_ctor_set(v___x_2649_, 2, v___x_2648_);
if (lean_obj_tag(v_vis_x3f_1901_) == 1)
{
lean_object* v_val_2650_; lean_object* v___x_2651_; 
v_val_2650_ = lean_ctor_get(v_vis_x3f_1901_, 0);
lean_inc(v_val_2650_);
v___x_2651_ = l_Array_mkArray1___redArg(v_val_2650_);
v___y_2429_ = v___x_2641_;
v___y_2430_ = v_currRecDepth_2637_;
v___y_2431_ = v_maxRecDepth_2638_;
v___y_2432_ = v___x_2642_;
v___y_2433_ = v___x_2643_;
v___y_2434_ = v___x_2640_;
v___y_2435_ = v_ref_2639_;
v___y_2436_ = v___x_2647_;
v___y_2437_ = v___x_2645_;
v___y_2438_ = v___x_2644_;
v___y_2439_ = v_quotContext_2635_;
v___y_2440_ = v___x_2646_;
v___y_2441_ = v_currMacroScope_2636_;
v___y_2442_ = v___x_2648_;
v___y_2443_ = v_methods_2634_;
v___y_2444_ = v___x_2649_;
v___y_2445_ = v___x_2651_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2429_ = v___x_2641_;
v___y_2430_ = v_currRecDepth_2637_;
v___y_2431_ = v_maxRecDepth_2638_;
v___y_2432_ = v___x_2642_;
v___y_2433_ = v___x_2643_;
v___y_2434_ = v___x_2640_;
v___y_2435_ = v_ref_2639_;
v___y_2436_ = v___x_2647_;
v___y_2437_ = v___x_2645_;
v___y_2438_ = v___x_2644_;
v___y_2439_ = v_quotContext_2635_;
v___y_2440_ = v___x_2646_;
v___y_2441_ = v_currMacroScope_2636_;
v___y_2442_ = v___x_2648_;
v___y_2443_ = v_methods_2634_;
v___y_2444_ = v___x_2649_;
v___y_2445_ = v___x_2652_;
goto v___jp_2428_;
}
}
}
}
else
{
lean_object* v___x_2670_; 
lean_dec(v_vis_x3f_1901_);
lean_dec(v___x_1900_);
lean_dec(v_structTy_1899_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_b_1906_);
lean_ctor_set(v___x_2670_, 1, v___y_1908_);
return v___x_2670_;
}
v___jp_1909_:
{
size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1904_, v___x_1912_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1899_, v___x_1900_, v_vis_x3f_1901_, v_structId_1902_, v_as_1903_, v___x_1913_, v_stop_1905_, v_a_1910_, v___y_1907_, v_a_1911_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___boxed(lean_object* v_structTy_2671_, lean_object* v___x_2672_, lean_object* v_vis_x3f_2673_, lean_object* v_structId_2674_, lean_object* v_as_2675_, lean_object* v_i_2676_, lean_object* v_stop_2677_, lean_object* v_b_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
size_t v_i_boxed_2681_; size_t v_stop_boxed_2682_; lean_object* v_res_2683_; 
v_i_boxed_2681_ = lean_unbox_usize(v_i_2676_);
lean_dec(v_i_2676_);
v_stop_boxed_2682_ = lean_unbox_usize(v_stop_2677_);
lean_dec(v_stop_2677_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2671_, v___x_2672_, v_vis_x3f_2673_, v_structId_2674_, v_as_2675_, v_i_boxed_2681_, v_stop_boxed_2682_, v_b_2678_, v___y_2679_, v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v_as_2675_);
lean_dec(v_structId_2674_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(size_t v_sz_2684_, size_t v_i_2685_, lean_object* v_bs_2686_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_usize_dec_lt(v_i_2685_, v_sz_2684_);
if (v___x_2687_ == 0)
{
return v_bs_2686_;
}
else
{
lean_object* v_v_2688_; lean_object* v_id_2689_; lean_object* v___x_2690_; lean_object* v_bs_x27_2691_; size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v_v_2688_ = lean_array_uget_borrowed(v_bs_2686_, v_i_2685_);
v_id_2689_ = lean_ctor_get(v_v_2688_, 2);
lean_inc(v_id_2689_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v_bs_x27_2691_ = lean_array_uset(v_bs_2686_, v_i_2685_, v___x_2690_);
v___x_2692_ = ((size_t)1ULL);
v___x_2693_ = lean_usize_add(v_i_2685_, v___x_2692_);
v___x_2694_ = lean_array_uset(v_bs_x27_2691_, v_i_2685_, v_id_2689_);
v_i_2685_ = v___x_2693_;
v_bs_2686_ = v___x_2694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0___boxed(lean_object* v_sz_2696_, lean_object* v_i_2697_, lean_object* v_bs_2698_){
_start:
{
size_t v_sz_boxed_2699_; size_t v_i_boxed_2700_; lean_object* v_res_2701_; 
v_sz_boxed_2699_ = lean_unbox_usize(v_sz_2696_);
lean_dec(v_sz_2696_);
v_i_boxed_2700_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_res_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_boxed_2699_, v_i_boxed_2700_, v_bs_2698_);
return v_res_2701_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2710_ = l_Lean_firstFrontendMacroScope;
v___x_2711_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4));
v___x_2712_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1));
v___x_2713_ = l_Lean_addMacroScope(v___x_2712_, v___x_2711_, v___x_2710_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7));
v___x_2718_ = l_String_toRawSubstring_x27(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2725_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10));
v___x_2726_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5);
v___x_2727_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8);
v___x_2728_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_2729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
lean_ctor_set(v___x_2729_, 2, v___x_2726_);
lean_ctor_set(v___x_2729_, 3, v___x_2725_);
return v___x_2729_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_data_2732_; 
v___x_2730_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11);
v___x_2731_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v_data_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_data_2732_, 0, v___x_2731_);
lean_ctor_set(v_data_2732_, 1, v___x_2730_);
return v_data_2732_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2744_ = l_Lean_mkAtom(v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18));
v___x_2753_ = l_String_toRawSubstring_x27(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_2775_ = l_String_toRawSubstring_x27(v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2785_ = l_String_toRawSubstring_x27(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37));
v___x_2795_ = l_String_toRawSubstring_x27(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40));
v___x_2800_ = l_Lean_mkAtom(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2802_ = lean_unsigned_to_nat(3u);
v___x_2803_ = lean_mk_empty_array_with_capacity(v___x_2802_);
v___x_2804_ = lean_array_push(v___x_2803_, v___x_2801_);
return v___x_2804_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2806_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42);
v___x_2807_ = lean_array_push(v___x_2806_, v___x_2805_);
return v___x_2807_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2824_ = l_String_toRawSubstring_x27(v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(lean_object* v_vis_x3f_2851_, lean_object* v_structId_2852_, lean_object* v_structArity_2853_, lean_object* v_structTy_2854_, lean_object* v_views_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_quotContext_2858_; lean_object* v_currMacroScope_2859_; lean_object* v_ref_2860_; lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_3348_; 
v_quotContext_2858_ = lean_ctor_get(v_a_2856_, 1);
v_currMacroScope_2859_ = lean_ctor_get(v_a_2856_, 2);
v_ref_2860_ = lean_ctor_get(v_a_2856_, 5);
v___x_2861_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v_a_2857_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_a_2863_ = lean_ctor_get(v___x_2861_, 1);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_2865_ = v___x_2861_;
v_isShared_2866_ = v_isSharedCheck_3348_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_3348_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v_data_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; size_t v_sz_2880_; size_t v___x_2881_; lean_object* v___x_2882_; size_t v_sz_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v_a_3312_; lean_object* v_a_3313_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = 0;
v___x_2869_ = lean_box(0);
v_data_2870_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12);
v___x_2871_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2872_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2873_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13));
v___x_2874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
lean_inc_n(v_a_2862_, 9);
v___x_2875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2862_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2877_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_2878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2862_);
lean_ctor_set(v___x_2878_, 1, v___x_2876_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
v___x_2879_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14));
v_sz_2880_ = lean_array_size(v_views_2855_);
v___x_2881_ = ((size_t)0ULL);
lean_inc_ref(v_views_2855_);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_2880_, v___x_2881_, v_views_2855_);
v_sz_2883_ = lean_array_size(v___x_2882_);
lean_inc_ref_n(v___x_2878_, 2);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_2862_, v___x_2878_, v_sz_2883_, v___x_2881_, v___x_2882_);
v___x_2885_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2886_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15);
v___x_2887_ = l_Lean_mkSepArray(v___x_2884_, v___x_2886_);
lean_dec_ref(v___x_2884_);
v___x_2888_ = l_Array_append___redArg(v___x_2877_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2889_, 0, v_a_2862_);
lean_ctor_set(v___x_2889_, 1, v___x_2876_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
v___x_2890_ = l_Lean_Syntax_node1(v_a_2862_, v___x_2879_, v___x_2889_);
v___x_2891_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16));
v___x_2892_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17));
v___x_2893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2862_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_Syntax_node1(v_a_2862_, v___x_2876_, v___x_2893_);
v___x_2895_ = l_Lean_Syntax_node1(v_a_2862_, v___x_2891_, v___x_2894_);
v___x_2896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_3331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_a_2862_);
lean_ctor_set(v___x_3331_, 1, v___x_2896_);
v___x_3332_ = l_Lean_Syntax_node6(v_a_2862_, v___x_2873_, v___x_2875_, v___x_2878_, v___x_2890_, v___x_2895_, v___x_2878_, v___x_3331_);
v___x_3333_ = lean_array_get_size(v_views_2855_);
v___x_3334_ = lean_nat_dec_lt(v___x_2867_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_dec(v___x_3332_);
lean_dec_ref(v_views_2855_);
v_a_3312_ = v_data_2870_;
v_a_3313_ = v_a_2863_;
goto v___jp_3311_;
}
else
{
size_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_usize_of_nat(v___x_3333_);
lean_inc(v_vis_x3f_2851_);
lean_inc(v_structTy_2854_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2854_, v___x_3332_, v_vis_x3f_2851_, v_structId_2852_, v_views_2855_, v___x_2881_, v___x_3335_, v_data_2870_, v_a_2856_, v_a_2863_);
lean_dec_ref(v_views_2855_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v_a_3338_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
v_a_3338_ = lean_ctor_get(v___x_3336_, 1);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3336_, 2);
v_a_3312_ = v_a_3337_;
v_a_3313_ = v_a_3338_;
goto v___jp_3311_;
}
else
{
lean_object* v_a_3339_; lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_del_object(v___x_2865_);
lean_dec(v_structTy_2854_);
lean_dec(v_structArity_2853_);
lean_dec(v_structId_2852_);
lean_dec(v_vis_x3f_2851_);
v_a_3339_ = lean_ctor_get(v___x_3336_, 0);
v_a_3340_ = lean_ctor_get(v___x_3336_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3336_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_inc(v_a_3339_);
lean_dec(v___x_3336_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3339_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
v___jp_2897_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2923_ = l_Array_append___redArg(v___x_2877_, v___y_2922_);
lean_dec_ref(v___y_2922_);
lean_inc_n(v___y_2906_, 27);
v___x_2924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2906_);
lean_ctor_set(v___x_2924_, 1, v___x_2876_);
lean_ctor_set(v___x_2924_, 2, v___x_2923_);
lean_inc_n(v___y_2919_, 16);
lean_inc(v___y_2917_);
v___x_2925_ = l_Lean_Syntax_node7(v___y_2906_, v___y_2917_, v___y_2919_, v___y_2919_, v___x_2924_, v___y_2919_, v___y_2919_, v___y_2919_, v___y_2919_);
v___x_2926_ = l_Lean_Syntax_node1(v___y_2906_, v___y_2914_, v___y_2919_);
v___x_2927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___y_2906_);
lean_ctor_set(v___x_2927_, 1, v___y_2905_);
v___x_2928_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2907_, v___y_2902_, v___y_2919_);
v___x_2929_ = l_Lean_Syntax_node1(v___y_2906_, v___x_2876_, v___x_2928_);
lean_inc_ref(v___y_2903_);
v___x_2930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___y_2906_);
lean_ctor_set(v___x_2930_, 1, v___y_2903_);
v___x_2931_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19);
v___x_2932_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20));
lean_inc(v_currMacroScope_2859_);
lean_inc(v_quotContext_2858_);
v___x_2933_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_2932_, v_currMacroScope_2859_);
v___x_2934_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24));
v___x_2935_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2935_, 0, v___y_2906_);
lean_ctor_set(v___x_2935_, 1, v___x_2931_);
lean_ctor_set(v___x_2935_, 2, v___x_2933_);
lean_ctor_set(v___x_2935_, 3, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_node1(v___y_2906_, v___x_2876_, v_structTy_2854_);
v___x_2937_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2909_, v___x_2935_, v___x_2936_);
v___x_2938_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2916_, v___x_2930_, v___x_2937_);
v___x_2939_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2910_, v___y_2919_, v___x_2938_);
lean_inc_ref(v___y_2915_);
v___x_2940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2906_);
lean_ctor_set(v___x_2940_, 1, v___y_2915_);
lean_inc_ref(v___y_2900_);
v___x_2941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___y_2906_);
lean_ctor_set(v___x_2941_, 1, v___y_2900_);
v___x_2942_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26));
v___x_2943_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28));
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___y_2906_);
lean_ctor_set(v___x_2944_, 1, v___x_2874_);
v___x_2945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___y_2906_);
lean_ctor_set(v___x_2945_, 1, v___x_2896_);
lean_inc_ref(v___x_2945_);
lean_inc_ref(v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node2(v___y_2906_, v___x_2943_, v___x_2944_, v___x_2945_);
v___x_2947_ = l_Lean_Syntax_node1(v___y_2906_, v___x_2879_, v___y_2919_);
v___x_2948_ = l_Lean_Syntax_node1(v___y_2906_, v___x_2891_, v___y_2919_);
v___x_2949_ = l_Lean_Syntax_node6(v___y_2906_, v___x_2873_, v___x_2944_, v___y_2919_, v___x_2947_, v___x_2948_, v___y_2919_, v___x_2945_);
v___x_2950_ = l_Lean_Syntax_node2(v___y_2906_, v___x_2942_, v___x_2946_, v___x_2949_);
v___x_2951_ = l_Lean_Syntax_node1(v___y_2906_, v___x_2876_, v___x_2950_);
lean_inc_ref(v___y_2904_);
v___x_2952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___y_2906_);
lean_ctor_set(v___x_2952_, 1, v___y_2904_);
v___x_2953_ = l_Lean_Syntax_node3(v___y_2906_, v___y_2921_, v___x_2941_, v___x_2951_, v___x_2952_);
v___x_2954_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2899_, v___y_2919_, v___y_2919_);
v___x_2955_ = l_Lean_Syntax_node4(v___y_2906_, v___y_2913_, v___x_2940_, v___x_2953_, v___x_2954_, v___y_2919_);
v___x_2956_ = l_Lean_Syntax_node6(v___y_2906_, v___y_2908_, v___x_2926_, v___x_2927_, v___y_2919_, v___x_2929_, v___x_2939_, v___x_2955_);
lean_inc(v___y_2918_);
v___x_2957_ = l_Lean_Syntax_node2(v___y_2906_, v___y_2918_, v___x_2925_, v___x_2956_);
v___x_2958_ = lean_array_push(v___y_2911_, v___y_2898_);
v___x_2959_ = lean_array_push(v___x_2958_, v___y_2912_);
v___x_2960_ = lean_array_push(v___x_2959_, v___y_2920_);
v___x_2961_ = lean_array_push(v___x_2960_, v___x_2957_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v___y_2901_);
lean_ctor_set(v___x_2865_, 0, v___x_2961_);
v___x_2963_ = v___x_2865_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___y_2901_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
v___jp_2965_:
{
lean_object* v___x_2988_; lean_object* v_a_2989_; lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2988_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v___y_2986_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_n(v_a_2989_, 2);
v_a_2990_ = lean_ctor_get(v___x_2988_, 1);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2988_);
v___x_2991_ = l_Lean_mkIdentFrom(v_structId_2852_, v___y_2987_, v___x_2868_);
lean_dec(v_structId_2852_);
v___x_2992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2992_, 0, v_a_2989_);
lean_ctor_set(v___x_2992_, 1, v___x_2876_);
lean_ctor_set(v___x_2992_, 2, v___x_2877_);
if (lean_obj_tag(v_vis_x3f_2851_) == 1)
{
lean_object* v_val_2993_; lean_object* v___x_2994_; 
v_val_2993_ = lean_ctor_get(v_vis_x3f_2851_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v_vis_x3f_2851_, 1);
v___x_2994_ = l_Array_mkArray1___redArg(v_val_2993_);
v___y_2898_ = v___y_2966_;
v___y_2899_ = v___y_2967_;
v___y_2900_ = v___y_2968_;
v___y_2901_ = v_a_2990_;
v___y_2902_ = v___x_2991_;
v___y_2903_ = v___y_2969_;
v___y_2904_ = v___y_2970_;
v___y_2905_ = v___y_2971_;
v___y_2906_ = v_a_2989_;
v___y_2907_ = v___y_2972_;
v___y_2908_ = v___y_2973_;
v___y_2909_ = v___y_2974_;
v___y_2910_ = v___y_2975_;
v___y_2911_ = v___y_2976_;
v___y_2912_ = v___y_2977_;
v___y_2913_ = v___y_2978_;
v___y_2914_ = v___y_2979_;
v___y_2915_ = v___y_2980_;
v___y_2916_ = v___y_2981_;
v___y_2917_ = v___y_2982_;
v___y_2918_ = v___y_2983_;
v___y_2919_ = v___x_2992_;
v___y_2920_ = v___y_2985_;
v___y_2921_ = v___y_2984_;
v___y_2922_ = v___x_2994_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2995_; 
lean_dec(v_vis_x3f_2851_);
v___x_2995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2898_ = v___y_2966_;
v___y_2899_ = v___y_2967_;
v___y_2900_ = v___y_2968_;
v___y_2901_ = v_a_2990_;
v___y_2902_ = v___x_2991_;
v___y_2903_ = v___y_2969_;
v___y_2904_ = v___y_2970_;
v___y_2905_ = v___y_2971_;
v___y_2906_ = v_a_2989_;
v___y_2907_ = v___y_2972_;
v___y_2908_ = v___y_2973_;
v___y_2909_ = v___y_2974_;
v___y_2910_ = v___y_2975_;
v___y_2911_ = v___y_2976_;
v___y_2912_ = v___y_2977_;
v___y_2913_ = v___y_2978_;
v___y_2914_ = v___y_2979_;
v___y_2915_ = v___y_2980_;
v___y_2916_ = v___y_2981_;
v___y_2917_ = v___y_2982_;
v___y_2918_ = v___y_2983_;
v___y_2919_ = v___x_2992_;
v___y_2920_ = v___y_2985_;
v___y_2921_ = v___y_2984_;
v___y_2922_ = v___x_2995_;
goto v___jp_2897_;
}
}
v___jp_2996_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3025_ = l_Array_append___redArg(v___x_2877_, v___y_3024_);
lean_dec_ref(v___y_3024_);
lean_inc_n(v___y_3001_, 16);
v___x_3026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3026_, 0, v___y_3001_);
lean_ctor_set(v___x_3026_, 1, v___x_2876_);
lean_ctor_set(v___x_3026_, 2, v___x_3025_);
lean_inc_n(v___y_3004_, 12);
lean_inc(v___y_3014_);
v___x_3027_ = l_Lean_Syntax_node7(v___y_3001_, v___y_3014_, v___y_3004_, v___y_3004_, v___x_3026_, v___y_3004_, v___y_3004_, v___y_3004_, v___y_3004_);
lean_inc(v___y_3022_);
v___x_3028_ = l_Lean_Syntax_node1(v___y_3001_, v___y_3022_, v___y_3004_);
lean_inc_ref(v___y_3003_);
v___x_3029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___y_3001_);
lean_ctor_set(v___x_3029_, 1, v___y_3003_);
lean_inc(v___y_3006_);
v___x_3030_ = l_Lean_Syntax_node2(v___y_3001_, v___y_3006_, v___y_3013_, v___y_3004_);
v___x_3031_ = l_Lean_Syntax_node1(v___y_3001_, v___x_2876_, v___x_3030_);
lean_inc_ref(v___y_3000_);
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___y_3001_);
lean_ctor_set(v___x_3032_, 1, v___y_3000_);
v___x_3033_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_3034_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30);
v___x_3035_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31));
lean_inc(v_currMacroScope_2859_);
lean_inc(v_quotContext_2858_);
v___x_3036_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_3035_, v_currMacroScope_2859_);
lean_inc_ref(v___y_3012_);
v___x_3037_ = l_Lean_Name_mkStr2(v___y_3012_, v___x_3033_);
lean_inc(v___x_3037_);
v___x_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_2869_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
v___x_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_2869_);
v___x_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3038_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3001_);
lean_ctor_set(v___x_3042_, 1, v___x_3034_);
lean_ctor_set(v___x_3042_, 2, v___x_3036_);
lean_ctor_set(v___x_3042_, 3, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_node1(v___y_3001_, v___x_2876_, v___y_3017_);
lean_inc(v___y_3020_);
v___x_3044_ = l_Lean_Syntax_node2(v___y_3001_, v___y_3020_, v___x_3042_, v___x_3043_);
lean_inc(v___y_3011_);
v___x_3045_ = l_Lean_Syntax_node2(v___y_3001_, v___y_3011_, v___x_3032_, v___x_3044_);
lean_inc(v___y_3019_);
v___x_3046_ = l_Lean_Syntax_node2(v___y_3001_, v___y_3019_, v___y_3004_, v___x_3045_);
lean_inc_ref(v___y_3010_);
v___x_3047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___y_3001_);
lean_ctor_set(v___x_3047_, 1, v___y_3010_);
lean_inc(v___y_2997_);
v___x_3048_ = l_Lean_Syntax_node2(v___y_3001_, v___y_2997_, v___y_3004_, v___y_3004_);
lean_inc(v___y_3009_);
v___x_3049_ = l_Lean_Syntax_node4(v___y_3001_, v___y_3009_, v___x_3047_, v___y_3005_, v___x_3048_, v___y_3004_);
lean_inc(v___y_3018_);
v___x_3050_ = l_Lean_Syntax_node6(v___y_3001_, v___y_3018_, v___x_3028_, v___x_3029_, v___y_3004_, v___x_3031_, v___x_3046_, v___x_3049_);
lean_inc(v___y_3015_);
v___x_3051_ = l_Lean_Syntax_node2(v___y_3001_, v___y_3015_, v___x_3027_, v___x_3050_);
v___x_3052_ = l_Lean_Name_hasMacroScopes(v___y_3007_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v___y_3007_);
v___y_2966_ = v___y_2998_;
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2999_;
v___y_2969_ = v___y_3000_;
v___y_2970_ = v___y_3002_;
v___y_2971_ = v___y_3003_;
v___y_2972_ = v___y_3006_;
v___y_2973_ = v___y_3018_;
v___y_2974_ = v___y_3020_;
v___y_2975_ = v___y_3019_;
v___y_2976_ = v___y_3021_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3009_;
v___y_2979_ = v___y_3022_;
v___y_2980_ = v___y_3010_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___y_3014_;
v___y_2983_ = v___y_3015_;
v___y_2984_ = v___y_3016_;
v___y_2985_ = v___x_3051_;
v___y_2986_ = v___y_3023_;
v___y_2987_ = v___x_3053_;
goto v___jp_2965_;
}
else
{
lean_object* v_view_3054_; lean_object* v_name_3055_; lean_object* v_imported_3056_; lean_object* v_ctx_3057_; lean_object* v_scopes_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3067_; 
v_view_3054_ = l_Lean_extractMacroScopes(v___y_3007_);
v_name_3055_ = lean_ctor_get(v_view_3054_, 0);
v_imported_3056_ = lean_ctor_get(v_view_3054_, 1);
v_ctx_3057_ = lean_ctor_get(v_view_3054_, 2);
v_scopes_3058_ = lean_ctor_get(v_view_3054_, 3);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_view_3054_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3060_ = v_view_3054_;
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_scopes_3058_);
lean_inc(v_ctx_3057_);
lean_inc(v_imported_3056_);
lean_inc(v_name_3055_);
lean_dec(v_view_3054_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v_name_3055_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_imported_3056_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v_ctx_3057_);
lean_ctor_set(v_reuseFailAlloc_3066_, 3, v_scopes_3058_);
v___x_3064_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_MacroScopesView_review(v___x_3064_);
v___y_2966_ = v___y_2998_;
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2999_;
v___y_2969_ = v___y_3000_;
v___y_2970_ = v___y_3002_;
v___y_2971_ = v___y_3003_;
v___y_2972_ = v___y_3006_;
v___y_2973_ = v___y_3018_;
v___y_2974_ = v___y_3020_;
v___y_2975_ = v___y_3019_;
v___y_2976_ = v___y_3021_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3009_;
v___y_2979_ = v___y_3022_;
v___y_2980_ = v___y_3010_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___y_3014_;
v___y_2983_ = v___y_3015_;
v___y_2984_ = v___y_3016_;
v___y_2985_ = v___x_3051_;
v___y_2986_ = v___y_3023_;
v___y_2987_ = v___x_3065_;
goto v___jp_2965_;
}
}
}
}
v___jp_3068_:
{
lean_object* v___x_3093_; lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3144_; 
v___x_3093_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v___y_3090_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_a_3095_ = lean_ctor_get(v___x_3093_, 1);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3097_ = v___x_3093_;
v_isShared_3098_ = v_isSharedCheck_3144_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3144_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33));
lean_inc(v_a_3094_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 2);
lean_ctor_set(v___x_3097_, 1, v___x_2874_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___x_2874_);
v___x_3101_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v_a_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_inc_n(v_a_3094_, 17);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v_a_3094_);
lean_ctor_set(v___x_3102_, 1, v___x_2876_);
lean_ctor_set(v___x_3102_, 2, v___x_2877_);
v___x_3103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1));
v___x_3104_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2));
v___x_3105_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34);
v___x_3106_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35));
lean_inc_n(v_currMacroScope_2859_, 2);
lean_inc_n(v_quotContext_2858_, 2);
v___x_3107_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_3106_, v_currMacroScope_2859_);
v___x_3108_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3108_, 0, v_a_3094_);
lean_ctor_set(v___x_3108_, 1, v___x_3105_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
lean_ctor_set(v___x_3108_, 3, v___x_2869_);
lean_inc_ref_n(v___x_3102_, 10);
v___x_3109_ = l_Lean_Syntax_node2(v_a_3094_, v___x_3104_, v___x_3108_, v___x_3102_);
v___x_3110_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36));
lean_inc_ref(v___y_3085_);
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_a_3094_);
lean_ctor_set(v___x_3111_, 1, v___y_3085_);
lean_inc_ref(v___x_3111_);
v___x_3112_ = l_Lean_Syntax_node3(v_a_3094_, v___x_3110_, v___x_3111_, v___x_3102_, v___y_3075_);
v___x_3113_ = l_Lean_Syntax_node3(v_a_3094_, v___x_2876_, v___x_3102_, v___x_3102_, v___x_3112_);
v___x_3114_ = l_Lean_Syntax_node2(v_a_3094_, v___x_3103_, v___x_3109_, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_a_3094_);
lean_ctor_set(v___x_3115_, 1, v___x_2885_);
v___x_3116_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38);
v___x_3117_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39));
v___x_3118_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_3117_, v_currMacroScope_2859_);
v___x_3119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3119_, 0, v_a_3094_);
lean_ctor_set(v___x_3119_, 1, v___x_3116_);
lean_ctor_set(v___x_3119_, 2, v___x_3118_);
lean_ctor_set(v___x_3119_, 3, v___x_2869_);
v___x_3120_ = l_Lean_Syntax_node2(v_a_3094_, v___x_3104_, v___x_3119_, v___x_3102_);
v___x_3121_ = l_Nat_reprFast(v_structArity_2853_);
v___x_3122_ = lean_box(2);
v___x_3123_ = l_Lean_Syntax_mkNumLit(v___x_3121_, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_node3(v_a_3094_, v___x_3110_, v___x_3111_, v___x_3102_, v___x_3123_);
v___x_3125_ = l_Lean_Syntax_node3(v_a_3094_, v___x_2876_, v___x_3102_, v___x_3102_, v___x_3124_);
v___x_3126_ = l_Lean_Syntax_node2(v_a_3094_, v___x_3103_, v___x_3120_, v___x_3125_);
v___x_3127_ = l_Lean_Syntax_node3(v_a_3094_, v___x_2876_, v___x_3114_, v___x_3115_, v___x_3126_);
v___x_3128_ = l_Lean_Syntax_node1(v_a_3094_, v___x_2879_, v___x_3127_);
v___x_3129_ = l_Lean_Syntax_node1(v_a_3094_, v___x_2891_, v___x_3102_);
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3094_);
lean_ctor_set(v___x_3130_, 1, v___x_2896_);
v___x_3131_ = l_Lean_Syntax_node6(v_a_3094_, v___x_2873_, v___x_3101_, v___x_3102_, v___x_3128_, v___x_3129_, v___x_3102_, v___x_3130_);
v___x_3132_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v_a_3095_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc_n(v_a_3133_, 2);
v_a_3134_ = lean_ctor_get(v___x_3132_, 1);
lean_inc(v_a_3134_);
lean_dec_ref(v___x_3132_);
v___x_3135_ = l_Lean_mkIdentFrom(v_structId_2852_, v___y_3092_, v___x_2868_);
v___x_3136_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43);
lean_inc(v_structId_2852_);
v___x_3137_ = lean_array_push(v___x_3136_, v_structId_2852_);
v___x_3138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3122_);
lean_ctor_set(v___x_3138_, 1, v___x_3099_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3139_, 0, v_a_3133_);
lean_ctor_set(v___x_3139_, 1, v___x_2876_);
lean_ctor_set(v___x_3139_, 2, v___x_2877_);
if (lean_obj_tag(v_vis_x3f_2851_) == 1)
{
lean_object* v_val_3140_; lean_object* v___x_3141_; 
v_val_3140_ = lean_ctor_get(v_vis_x3f_2851_, 0);
lean_inc(v_val_3140_);
v___x_3141_ = l_Array_mkArray1___redArg(v_val_3140_);
v___y_2997_ = v___y_3069_;
v___y_2998_ = v___y_3070_;
v___y_2999_ = v___y_3071_;
v___y_3000_ = v___y_3072_;
v___y_3001_ = v_a_3133_;
v___y_3002_ = v___y_3073_;
v___y_3003_ = v___y_3074_;
v___y_3004_ = v___x_3139_;
v___y_3005_ = v___x_3131_;
v___y_3006_ = v___y_3076_;
v___y_3007_ = v___y_3078_;
v___y_3008_ = v___y_3082_;
v___y_3009_ = v___y_3083_;
v___y_3010_ = v___y_3085_;
v___y_3011_ = v___y_3086_;
v___y_3012_ = v___y_3088_;
v___y_3013_ = v___x_3135_;
v___y_3014_ = v___y_3087_;
v___y_3015_ = v___y_3089_;
v___y_3016_ = v___y_3091_;
v___y_3017_ = v___x_3138_;
v___y_3018_ = v___y_3077_;
v___y_3019_ = v___y_3080_;
v___y_3020_ = v___y_3079_;
v___y_3021_ = v___y_3081_;
v___y_3022_ = v___y_3084_;
v___y_3023_ = v_a_3134_;
v___y_3024_ = v___x_3141_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3142_; 
v___x_3142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2997_ = v___y_3069_;
v___y_2998_ = v___y_3070_;
v___y_2999_ = v___y_3071_;
v___y_3000_ = v___y_3072_;
v___y_3001_ = v_a_3133_;
v___y_3002_ = v___y_3073_;
v___y_3003_ = v___y_3074_;
v___y_3004_ = v___x_3139_;
v___y_3005_ = v___x_3131_;
v___y_3006_ = v___y_3076_;
v___y_3007_ = v___y_3078_;
v___y_3008_ = v___y_3082_;
v___y_3009_ = v___y_3083_;
v___y_3010_ = v___y_3085_;
v___y_3011_ = v___y_3086_;
v___y_3012_ = v___y_3088_;
v___y_3013_ = v___x_3135_;
v___y_3014_ = v___y_3087_;
v___y_3015_ = v___y_3089_;
v___y_3016_ = v___y_3091_;
v___y_3017_ = v___x_3138_;
v___y_3018_ = v___y_3077_;
v___y_3019_ = v___y_3080_;
v___y_3020_ = v___y_3079_;
v___y_3021_ = v___y_3081_;
v___y_3022_ = v___y_3084_;
v___y_3023_ = v_a_3134_;
v___y_3024_ = v___x_3142_;
goto v___jp_2996_;
}
}
}
}
v___jp_3145_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3162_ = l_Array_append___redArg(v___x_2877_, v___y_3161_);
lean_dec_ref(v___y_3161_);
lean_inc_n(v___y_3153_, 20);
v___x_3163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3163_, 0, v___y_3153_);
lean_ctor_set(v___x_3163_, 1, v___x_2876_);
lean_ctor_set(v___x_3163_, 2, v___x_3162_);
lean_inc_n(v___y_3151_, 12);
lean_inc(v___y_3158_);
v___x_3164_ = l_Lean_Syntax_node7(v___y_3153_, v___y_3158_, v___y_3151_, v___y_3151_, v___x_3163_, v___y_3151_, v___y_3151_, v___y_3151_, v___y_3151_);
v___x_3165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_3157_, 2);
v___x_3166_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3157_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44));
v___x_3168_ = l_Lean_Syntax_node1(v___y_3153_, v___x_3167_, v___y_3151_);
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3153_);
lean_ctor_set(v___x_3169_, 1, v___x_3165_);
lean_inc(v___y_3149_);
v___x_3170_ = l_Lean_Syntax_node2(v___y_3153_, v___y_3149_, v___y_3155_, v___y_3151_);
v___x_3171_ = l_Lean_Syntax_node1(v___y_3153_, v___x_2876_, v___x_3170_);
v___x_3172_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_3173_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3157_, v___x_3172_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
v___x_3175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3153_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
v___x_3178_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47);
v___x_3179_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48));
lean_inc(v_currMacroScope_2859_);
lean_inc(v_quotContext_2858_);
v___x_3180_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_3179_, v_currMacroScope_2859_);
v___x_3181_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_3182_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53));
v___x_3183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3183_, 0, v___y_3153_);
lean_ctor_set(v___x_3183_, 1, v___x_3178_);
lean_ctor_set(v___x_3183_, 2, v___x_3180_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
lean_inc(v_structTy_2854_);
v___x_3184_ = l_Lean_Syntax_node1(v___y_3153_, v___x_2876_, v_structTy_2854_);
v___x_3185_ = l_Lean_Syntax_node2(v___y_3153_, v___x_3177_, v___x_3183_, v___x_3184_);
v___x_3186_ = l_Lean_Syntax_node2(v___y_3153_, v___x_3174_, v___x_3176_, v___x_3185_);
lean_inc(v___x_3173_);
v___x_3187_ = l_Lean_Syntax_node2(v___y_3153_, v___x_3173_, v___y_3151_, v___x_3186_);
lean_inc_ref(v___y_3156_);
v___x_3188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___y_3153_);
lean_ctor_set(v___x_3188_, 1, v___y_3156_);
v___x_3189_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54));
v___x_3190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_3191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3153_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
lean_inc(v___y_3148_);
v___x_3192_ = l_Lean_Syntax_node1(v___y_3153_, v___x_2876_, v___y_3148_);
v___x_3193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3153_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_Syntax_node3(v___y_3153_, v___x_3189_, v___x_3191_, v___x_3192_, v___x_3194_);
lean_inc(v___y_3146_);
v___x_3196_ = l_Lean_Syntax_node2(v___y_3153_, v___y_3146_, v___y_3151_, v___y_3151_);
lean_inc(v___y_3154_);
v___x_3197_ = l_Lean_Syntax_node4(v___y_3153_, v___y_3154_, v___x_3188_, v___x_3195_, v___x_3196_, v___y_3151_);
lean_inc(v___x_3166_);
v___x_3198_ = l_Lean_Syntax_node6(v___y_3153_, v___x_3166_, v___x_3168_, v___x_3169_, v___y_3151_, v___x_3171_, v___x_3187_, v___x_3197_);
lean_inc(v___y_3160_);
v___x_3199_ = l_Lean_Syntax_node2(v___y_3153_, v___y_3160_, v___x_3164_, v___x_3198_);
v___x_3200_ = l_Lean_Name_hasMacroScopes(v___y_3150_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_inc(v___y_3150_);
v___x_3201_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v___y_3150_);
v___y_3069_ = v___y_3146_;
v___y_3070_ = v___y_3147_;
v___y_3071_ = v___x_3190_;
v___y_3072_ = v___x_3175_;
v___y_3073_ = v___x_3193_;
v___y_3074_ = v___x_3165_;
v___y_3075_ = v___y_3148_;
v___y_3076_ = v___y_3149_;
v___y_3077_ = v___x_3166_;
v___y_3078_ = v___y_3150_;
v___y_3079_ = v___x_3177_;
v___y_3080_ = v___x_3173_;
v___y_3081_ = v___y_3152_;
v___y_3082_ = v___x_3199_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___x_3167_;
v___y_3085_ = v___y_3156_;
v___y_3086_ = v___x_3174_;
v___y_3087_ = v___y_3158_;
v___y_3088_ = v___x_3181_;
v___y_3089_ = v___y_3160_;
v___y_3090_ = v___y_3159_;
v___y_3091_ = v___x_3189_;
v___y_3092_ = v___x_3201_;
goto v___jp_3068_;
}
else
{
lean_object* v_view_3202_; lean_object* v_name_3203_; lean_object* v_imported_3204_; lean_object* v_ctx_3205_; lean_object* v_scopes_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3215_; 
lean_inc(v___y_3150_);
v_view_3202_ = l_Lean_extractMacroScopes(v___y_3150_);
v_name_3203_ = lean_ctor_get(v_view_3202_, 0);
v_imported_3204_ = lean_ctor_get(v_view_3202_, 1);
v_ctx_3205_ = lean_ctor_get(v_view_3202_, 2);
v_scopes_3206_ = lean_ctor_get(v_view_3202_, 3);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_view_3202_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3208_ = v_view_3202_;
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_scopes_3206_);
lean_inc(v_ctx_3205_);
lean_inc(v_imported_3204_);
lean_inc(v_name_3203_);
lean_dec(v_view_3202_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v_name_3203_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_imported_3204_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_ctx_3205_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_scopes_3206_);
v___x_3212_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_MacroScopesView_review(v___x_3212_);
v___y_3069_ = v___y_3146_;
v___y_3070_ = v___y_3147_;
v___y_3071_ = v___x_3190_;
v___y_3072_ = v___x_3175_;
v___y_3073_ = v___x_3193_;
v___y_3074_ = v___x_3165_;
v___y_3075_ = v___y_3148_;
v___y_3076_ = v___y_3149_;
v___y_3077_ = v___x_3166_;
v___y_3078_ = v___y_3150_;
v___y_3079_ = v___x_3177_;
v___y_3080_ = v___x_3173_;
v___y_3081_ = v___y_3152_;
v___y_3082_ = v___x_3199_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___x_3167_;
v___y_3085_ = v___y_3156_;
v___y_3086_ = v___x_3174_;
v___y_3087_ = v___y_3158_;
v___y_3088_ = v___x_3181_;
v___y_3089_ = v___y_3160_;
v___y_3090_ = v___y_3159_;
v___y_3091_ = v___x_3189_;
v___y_3092_ = v___x_3213_;
goto v___jp_3068_;
}
}
}
}
v___jp_3216_:
{
lean_object* v___x_3230_; lean_object* v_a_3231_; lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3230_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v___y_3228_);
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_n(v_a_3231_, 2);
v_a_3232_ = lean_ctor_get(v___x_3230_, 1);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3230_);
v___x_3233_ = l_Lean_mkIdentFrom(v_structId_2852_, v___y_3229_, v___x_2868_);
v___x_3234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3234_, 0, v_a_3231_);
lean_ctor_set(v___x_3234_, 1, v___x_2876_);
lean_ctor_set(v___x_3234_, 2, v___x_2877_);
if (lean_obj_tag(v_vis_x3f_2851_) == 1)
{
lean_object* v_val_3235_; lean_object* v___x_3236_; 
v_val_3235_ = lean_ctor_get(v_vis_x3f_2851_, 0);
lean_inc(v_val_3235_);
v___x_3236_ = l_Array_mkArray1___redArg(v_val_3235_);
v___y_3146_ = v___y_3219_;
v___y_3147_ = v___y_3218_;
v___y_3148_ = v___y_3223_;
v___y_3149_ = v___y_3225_;
v___y_3150_ = v___y_3227_;
v___y_3151_ = v___x_3234_;
v___y_3152_ = v___y_3217_;
v___y_3153_ = v_a_3231_;
v___y_3154_ = v___y_3220_;
v___y_3155_ = v___x_3233_;
v___y_3156_ = v___y_3221_;
v___y_3157_ = v___y_3222_;
v___y_3158_ = v___y_3224_;
v___y_3159_ = v_a_3232_;
v___y_3160_ = v___y_3226_;
v___y_3161_ = v___x_3236_;
goto v___jp_3145_;
}
else
{
lean_object* v___x_3237_; 
v___x_3237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3146_ = v___y_3219_;
v___y_3147_ = v___y_3218_;
v___y_3148_ = v___y_3223_;
v___y_3149_ = v___y_3225_;
v___y_3150_ = v___y_3227_;
v___y_3151_ = v___x_3234_;
v___y_3152_ = v___y_3217_;
v___y_3153_ = v_a_3231_;
v___y_3154_ = v___y_3220_;
v___y_3155_ = v___x_3233_;
v___y_3156_ = v___y_3221_;
v___y_3157_ = v___y_3222_;
v___y_3158_ = v___y_3224_;
v___y_3159_ = v_a_3232_;
v___y_3160_ = v___y_3226_;
v___y_3161_ = v___x_3237_;
goto v___jp_3145_;
}
}
v___jp_3238_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_cmds_3262_; lean_object* v_fields_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3294_; 
v___x_3249_ = l_Array_append___redArg(v___x_2877_, v___y_3248_);
lean_dec_ref(v___y_3248_);
lean_inc_n(v___y_3240_, 5);
v___x_3250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3250_, 0, v___y_3240_);
lean_ctor_set(v___x_3250_, 1, v___x_2876_);
lean_ctor_set(v___x_3250_, 2, v___x_3249_);
lean_inc_n(v___y_3243_, 9);
lean_inc(v___y_3244_);
v___x_3251_ = l_Lean_Syntax_node7(v___y_3240_, v___y_3244_, v___y_3243_, v___y_3243_, v___x_3250_, v___y_3243_, v___y_3243_, v___y_3243_, v___y_3243_);
v___x_3252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_3242_, 3);
v___x_3253_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3242_, v___x_3252_);
v___x_3254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_3255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___y_3240_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_3257_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3242_, v___x_3256_);
lean_inc(v___y_3241_);
lean_inc(v___x_3257_);
v___x_3258_ = l_Lean_Syntax_node2(v___y_3240_, v___x_3257_, v___y_3241_, v___y_3243_);
v___x_3259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_3260_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3242_, v___x_3259_);
v___x_3261_ = l_Lean_Syntax_node2(v___y_3240_, v___x_3260_, v___y_3243_, v___y_3243_);
v_cmds_3262_ = lean_ctor_get(v___y_3239_, 0);
v_fields_3263_ = lean_ctor_get(v___y_3239_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___y_3239_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3265_ = v___y_3239_;
v_isShared_3266_ = v_isSharedCheck_3294_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_fields_3263_);
lean_inc(v_cmds_3262_);
lean_dec(v___y_3239_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3294_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
lean_inc_ref(v___y_3242_);
v___x_3268_ = l_Lean_Name_mkStr4(v___x_2871_, v___x_2872_, v___y_3242_, v___x_3267_);
v___x_3269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
lean_inc(v___y_3240_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 2);
lean_ctor_set(v___x_3265_, 1, v___x_3269_);
lean_ctor_set(v___x_3265_, 0, v___y_3240_);
v___x_3271_ = v___x_3265_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___y_3240_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3272_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55));
lean_inc_n(v___y_3243_, 3);
lean_inc_n(v___y_3240_, 3);
v___x_3273_ = l_Lean_Syntax_node2(v___y_3240_, v___x_3272_, v___y_3243_, v___y_3243_);
lean_inc(v___x_3268_);
v___x_3274_ = l_Lean_Syntax_node4(v___y_3240_, v___x_3268_, v___x_3271_, v_fields_3263_, v___x_3273_, v___y_3243_);
v___x_3275_ = l_Lean_Syntax_node5(v___y_3240_, v___x_3253_, v___x_3255_, v___x_3258_, v___x_3261_, v___x_3274_, v___y_3243_);
lean_inc(v___y_3246_);
v___x_3276_ = l_Lean_Syntax_node2(v___y_3240_, v___y_3246_, v___x_3251_, v___x_3275_);
v___x_3277_ = l_Lean_Name_hasMacroScopes(v___y_3245_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_inc(v___y_3245_);
v___x_3278_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v___y_3245_);
v___y_3217_ = v_cmds_3262_;
v___y_3218_ = v___x_3276_;
v___y_3219_ = v___x_3272_;
v___y_3220_ = v___x_3268_;
v___y_3221_ = v___x_3269_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3241_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___x_3257_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v___y_3245_;
v___y_3228_ = v___y_3247_;
v___y_3229_ = v___x_3278_;
goto v___jp_3216_;
}
else
{
lean_object* v_view_3279_; lean_object* v_name_3280_; lean_object* v_imported_3281_; lean_object* v_ctx_3282_; lean_object* v_scopes_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3292_; 
lean_inc(v___y_3245_);
v_view_3279_ = l_Lean_extractMacroScopes(v___y_3245_);
v_name_3280_ = lean_ctor_get(v_view_3279_, 0);
v_imported_3281_ = lean_ctor_get(v_view_3279_, 1);
v_ctx_3282_ = lean_ctor_get(v_view_3279_, 2);
v_scopes_3283_ = lean_ctor_get(v_view_3279_, 3);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_view_3279_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3285_ = v_view_3279_;
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_scopes_3283_);
lean_inc(v_ctx_3282_);
lean_inc(v_imported_3281_);
lean_inc(v_name_3280_);
lean_dec(v_view_3279_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v_name_3280_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3287_);
v___x_3289_ = v___x_3285_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_imported_3281_);
lean_ctor_set(v_reuseFailAlloc_3291_, 2, v_ctx_3282_);
lean_ctor_set(v_reuseFailAlloc_3291_, 3, v_scopes_3283_);
v___x_3289_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_MacroScopesView_review(v___x_3289_);
v___y_3217_ = v_cmds_3262_;
v___y_3218_ = v___x_3276_;
v___y_3219_ = v___x_3272_;
v___y_3220_ = v___x_3268_;
v___y_3221_ = v___x_3269_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3241_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___x_3257_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v___y_3245_;
v___y_3228_ = v___y_3247_;
v___y_3229_ = v___x_3290_;
goto v___jp_3216_;
}
}
}
}
}
}
v___jp_3295_:
{
lean_object* v___x_3300_; lean_object* v_a_3301_; lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3300_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2860_, v_a_2856_, v___y_3297_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_n(v_a_3301_, 2);
v_a_3302_ = lean_ctor_get(v___x_3300_, 1);
lean_inc(v_a_3302_);
lean_dec_ref(v___x_3300_);
v___x_3303_ = l_Lean_mkIdentFrom(v_structId_2852_, v___y_3299_, v___x_2868_);
v___x_3304_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_3306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3307_, 0, v_a_3301_);
lean_ctor_set(v___x_3307_, 1, v___x_2876_);
lean_ctor_set(v___x_3307_, 2, v___x_2877_);
if (lean_obj_tag(v_vis_x3f_2851_) == 1)
{
lean_object* v_val_3308_; lean_object* v___x_3309_; 
v_val_3308_ = lean_ctor_get(v_vis_x3f_2851_, 0);
lean_inc(v_val_3308_);
v___x_3309_ = l_Array_mkArray1___redArg(v_val_3308_);
v___y_3239_ = v___y_3296_;
v___y_3240_ = v_a_3301_;
v___y_3241_ = v___x_3303_;
v___y_3242_ = v___x_3304_;
v___y_3243_ = v___x_3307_;
v___y_3244_ = v___x_3306_;
v___y_3245_ = v___y_3298_;
v___y_3246_ = v___x_3305_;
v___y_3247_ = v_a_3302_;
v___y_3248_ = v___x_3309_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3239_ = v___y_3296_;
v___y_3240_ = v_a_3301_;
v___y_3241_ = v___x_3303_;
v___y_3242_ = v___x_3304_;
v___y_3243_ = v___x_3307_;
v___y_3244_ = v___x_3306_;
v___y_3245_ = v___y_3298_;
v___y_3246_ = v___x_3305_;
v___y_3247_ = v_a_3302_;
v___y_3248_ = v___x_3310_;
goto v___jp_3238_;
}
}
v___jp_3311_:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = l_Lean_TSyntax_getId(v_structId_2852_);
v___x_3315_ = l_Lean_Name_hasMacroScopes(v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_inc(v___x_3314_);
v___x_3316_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v___x_3314_);
v___y_3296_ = v_a_3312_;
v___y_3297_ = v_a_3313_;
v___y_3298_ = v___x_3314_;
v___y_3299_ = v___x_3316_;
goto v___jp_3295_;
}
else
{
lean_object* v_view_3317_; lean_object* v_name_3318_; lean_object* v_imported_3319_; lean_object* v_ctx_3320_; lean_object* v_scopes_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3330_; 
lean_inc(v___x_3314_);
v_view_3317_ = l_Lean_extractMacroScopes(v___x_3314_);
v_name_3318_ = lean_ctor_get(v_view_3317_, 0);
v_imported_3319_ = lean_ctor_get(v_view_3317_, 1);
v_ctx_3320_ = lean_ctor_get(v_view_3317_, 2);
v_scopes_3321_ = lean_ctor_get(v_view_3317_, 3);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_view_3317_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3323_ = v_view_3317_;
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_scopes_3321_);
lean_inc(v_ctx_3320_);
lean_inc(v_imported_3319_);
lean_inc(v_name_3318_);
lean_dec(v_view_3317_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v_name_3318_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_imported_3319_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_ctx_3320_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_scopes_3321_);
v___x_3327_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_MacroScopesView_review(v___x_3327_);
v___y_3296_ = v_a_3312_;
v___y_3297_ = v_a_3313_;
v___y_3298_ = v___x_3314_;
v___y_3299_ = v___x_3328_;
goto v___jp_3295_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___boxed(lean_object* v_vis_x3f_3349_, lean_object* v_structId_3350_, lean_object* v_structArity_3351_, lean_object* v_structTy_3352_, lean_object* v_views_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v_vis_x3f_3349_, v_structId_3350_, v_structArity_3351_, v_structTy_3352_, v_views_3353_, v_a_3354_, v_a_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(size_t v_sz_3357_, size_t v_i_3358_, lean_object* v_bs_3359_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_usize_dec_lt(v_i_3358_, v_sz_3357_);
if (v___x_3360_ == 0)
{
return v_bs_3359_;
}
else
{
lean_object* v_v_3361_; lean_object* v_id_3362_; lean_object* v___x_3363_; lean_object* v_bs_x27_3364_; size_t v___x_3365_; size_t v___x_3366_; lean_object* v___x_3367_; 
v_v_3361_ = lean_array_uget_borrowed(v_bs_3359_, v_i_3358_);
v_id_3362_ = lean_ctor_get(v_v_3361_, 1);
lean_inc(v_id_3362_);
v___x_3363_ = lean_unsigned_to_nat(0u);
v_bs_x27_3364_ = lean_array_uset(v_bs_3359_, v_i_3358_, v___x_3363_);
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3358_, v___x_3365_);
v___x_3367_ = lean_array_uset(v_bs_x27_3364_, v_i_3358_, v_id_3362_);
v_i_3358_ = v___x_3366_;
v_bs_3359_ = v___x_3367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0___boxed(lean_object* v_sz_3369_, lean_object* v_i_3370_, lean_object* v_bs_3371_){
_start:
{
size_t v_sz_boxed_3372_; size_t v_i_boxed_3373_; lean_object* v_res_3374_; 
v_sz_boxed_3372_ = lean_unbox_usize(v_sz_3369_);
lean_dec(v_sz_3369_);
v_i_boxed_3373_ = lean_unbox_usize(v_i_3370_);
lean_dec(v_i_3370_);
v_res_3374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_boxed_3372_, v_i_boxed_3373_, v_bs_3371_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView(lean_object* v_stx_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_methods_3398_; lean_object* v_quotContext_3399_; lean_object* v_currMacroScope_3400_; lean_object* v_currRecDepth_3401_; lean_object* v_maxRecDepth_3402_; lean_object* v_ref_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; lean_object* v_ref_3406_; lean_object* v___x_3407_; 
v_methods_3398_ = lean_ctor_get(v_a_3396_, 0);
v_quotContext_3399_ = lean_ctor_get(v_a_3396_, 1);
v_currMacroScope_3400_ = lean_ctor_get(v_a_3396_, 2);
v_currRecDepth_3401_ = lean_ctor_get(v_a_3396_, 3);
v_maxRecDepth_3402_ = lean_ctor_get(v_a_3396_, 4);
v_ref_3403_ = lean_ctor_get(v_a_3396_, 5);
v___x_3404_ = ((lean_object*)(l_Lake_configField___closed__2));
lean_inc(v_stx_3395_);
v___x_3405_ = l_Lean_Syntax_isOfKind(v_stx_3395_, v___x_3404_);
v_ref_3406_ = l_Lean_replaceRef(v_stx_3395_, v_ref_3403_);
lean_inc(v_maxRecDepth_3402_);
lean_inc(v_currRecDepth_3401_);
lean_inc(v_currMacroScope_3400_);
lean_inc(v_quotContext_3399_);
lean_inc(v_methods_3398_);
v___x_3407_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3407_, 0, v_methods_3398_);
lean_ctor_set(v___x_3407_, 1, v_quotContext_3399_);
lean_ctor_set(v___x_3407_, 2, v_currMacroScope_3400_);
lean_ctor_set(v___x_3407_, 3, v_currRecDepth_3401_);
lean_ctor_set(v___x_3407_, 4, v_maxRecDepth_3402_);
lean_ctor_set(v___x_3407_, 5, v_ref_3406_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v_stx_3395_);
v___x_3408_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3409_ = l_Lean_Macro_throwError___redArg(v___x_3408_, v___x_3407_, v_a_3397_);
lean_dec_ref_known(v___x_3407_, 6);
return v___x_3409_;
}
else
{
lean_object* v___x_3410_; lean_object* v_mods_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v_val_3423_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_val_x3f_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v_mods_3411_ = l_Lean_Syntax_getArg(v_stx_3395_, v___x_3410_);
v___x_3412_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_3413_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_3516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v_mods_3411_);
v___x_3517_ = l_Lean_Syntax_isOfKind(v_mods_3411_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3518_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3519_ = l_Lean_Macro_throwError___redArg(v___x_3518_, v___x_3407_, v_a_3397_);
lean_dec_ref_known(v___x_3407_, 6);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v_id_x3f_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3550_ = l_Lean_Syntax_getArg(v_stx_3395_, v___x_3520_);
v___x_3551_ = l_Lean_Syntax_isNone(v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3550_);
v___x_3553_ = l_Lean_Syntax_matchesNull(v___x_3550_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec(v___x_3550_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3554_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3555_ = l_Lean_Macro_throwError___redArg(v___x_3554_, v___x_3407_, v_a_3397_);
lean_dec_ref_known(v___x_3407_, 6);
return v___x_3555_;
}
else
{
lean_object* v_id_x3f_3556_; lean_object* v___x_3557_; 
v_id_x3f_3556_ = l_Lean_Syntax_getArg(v___x_3550_, v___x_3410_);
lean_dec(v___x_3550_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_id_x3f_3556_);
v_id_x3f_3522_ = v___x_3557_;
v___y_3523_ = v___x_3407_;
v___y_3524_ = v_a_3397_;
goto v___jp_3521_;
}
}
else
{
lean_object* v___x_3558_; 
lean_dec(v___x_3550_);
v___x_3558_ = lean_box(0);
v_id_x3f_3522_ = v___x_3558_;
v___y_3523_ = v___x_3407_;
v___y_3524_ = v_a_3397_;
goto v___jp_3521_;
}
v___jp_3521_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3525_ = lean_unsigned_to_nat(3u);
v___x_3526_ = l_Lean_Syntax_getArg(v_stx_3395_, v___x_3525_);
v___x_3527_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7));
lean_inc(v___x_3526_);
v___x_3528_ = l_Lean_Syntax_isOfKind(v___x_3526_, v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v___x_3526_);
lean_dec(v_id_x3f_3522_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3529_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3530_ = l_Lean_Macro_throwError___redArg(v___x_3529_, v___y_3523_, v___y_3524_);
lean_dec_ref(v___y_3523_);
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3531_ = l_Lean_Syntax_getArg(v___x_3526_, v___x_3520_);
v___x_3532_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_3533_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
lean_inc(v___x_3531_);
v___x_3534_ = l_Lean_Syntax_isOfKind(v___x_3531_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec(v___x_3531_);
lean_dec(v___x_3526_);
lean_dec(v_id_x3f_3522_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3535_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3536_ = l_Lean_Macro_throwError___redArg(v___x_3535_, v___y_3523_, v___y_3524_);
lean_dec_ref(v___y_3523_);
return v___x_3536_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v_rty_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3537_ = lean_unsigned_to_nat(2u);
v___x_3538_ = l_Lean_Syntax_getArg(v_stx_3395_, v___x_3537_);
v___x_3539_ = l_Lean_Syntax_getArg(v___x_3526_, v___x_3410_);
lean_dec(v___x_3526_);
v_rty_3540_ = l_Lean_Syntax_getArg(v___x_3531_, v___x_3520_);
lean_dec(v___x_3531_);
v___x_3541_ = lean_unsigned_to_nat(4u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_3395_, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_isNone(v___x_3542_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; 
lean_inc(v___x_3542_);
v___x_3544_ = l_Lean_Syntax_matchesNull(v___x_3542_, v___x_3537_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v___x_3542_);
lean_dec(v_rty_3540_);
lean_dec(v___x_3539_);
lean_dec(v___x_3538_);
lean_dec(v_id_x3f_3522_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3545_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3546_ = l_Lean_Macro_throwError___redArg(v___x_3545_, v___y_3523_, v___y_3524_);
lean_dec_ref(v___y_3523_);
return v___x_3546_;
}
else
{
lean_object* v_val_x3f_3547_; lean_object* v___x_3548_; 
v_val_x3f_3547_ = l_Lean_Syntax_getArg(v___x_3542_, v___x_3520_);
lean_dec(v___x_3542_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_val_x3f_3547_);
v___y_3485_ = v___x_3532_;
v___y_3486_ = v___x_3533_;
v___y_3487_ = v_id_x3f_3522_;
v___y_3488_ = v_rty_3540_;
v___y_3489_ = v___x_3538_;
v___y_3490_ = v___x_3539_;
v_val_x3f_3491_ = v___x_3548_;
v___y_3492_ = v___y_3523_;
v___y_3493_ = v___y_3524_;
goto v___jp_3484_;
}
}
else
{
lean_object* v___x_3549_; 
lean_dec(v___x_3542_);
v___x_3549_ = lean_box(0);
v___y_3485_ = v___x_3532_;
v___y_3486_ = v___x_3533_;
v___y_3487_ = v_id_x3f_3522_;
v___y_3488_ = v_rty_3540_;
v___y_3489_ = v___x_3538_;
v___y_3490_ = v___x_3539_;
v_val_x3f_3491_ = v___x_3549_;
v___y_3492_ = v___y_3523_;
v___y_3493_ = v___y_3524_;
goto v___jp_3484_;
}
}
}
}
}
v___jp_3414_:
{
lean_object* v_methods_3424_; lean_object* v_quotContext_3425_; lean_object* v_currMacroScope_3426_; lean_object* v_currRecDepth_3427_; lean_object* v_maxRecDepth_3428_; lean_object* v_ref_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3483_; 
v_methods_3424_ = lean_ctor_get(v___y_3419_, 0);
v_quotContext_3425_ = lean_ctor_get(v___y_3419_, 1);
v_currMacroScope_3426_ = lean_ctor_get(v___y_3419_, 2);
v_currRecDepth_3427_ = lean_ctor_get(v___y_3419_, 3);
v_maxRecDepth_3428_ = lean_ctor_get(v___y_3419_, 4);
v_ref_3429_ = lean_ctor_get(v___y_3419_, 5);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___y_3419_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3431_ = v___y_3419_;
v_isShared_3432_ = v_isSharedCheck_3483_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_ref_3429_);
lean_inc(v_maxRecDepth_3428_);
lean_inc(v_currRecDepth_3427_);
lean_inc(v_currMacroScope_3426_);
lean_inc(v_quotContext_3425_);
lean_inc(v_methods_3424_);
lean_dec(v___y_3419_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3483_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_ref_3433_; 
v_ref_3433_ = l_Lean_replaceRef(v_val_3423_, v_ref_3429_);
lean_dec(v_ref_3429_);
if (lean_obj_tag(v___y_3422_) == 1)
{
lean_object* v_val_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3477_; 
lean_del_object(v___x_3431_);
lean_dec(v_maxRecDepth_3428_);
lean_dec(v_currRecDepth_3427_);
lean_dec(v_currMacroScope_3426_);
lean_dec(v_quotContext_3425_);
lean_dec(v_methods_3424_);
v_val_3434_ = lean_ctor_get(v___y_3422_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___y_3422_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3436_ = v___y_3422_;
v_isShared_3437_ = v_isSharedCheck_3477_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_val_3434_);
lean_dec(v___y_3422_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3477_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v_sz_3447_; size_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3438_ = 0;
v___x_3439_ = l_Lean_SourceInfo_fromRef(v_ref_3433_, v___x_3438_);
lean_dec(v_ref_3433_);
v___x_3440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
lean_inc_ref_n(v___y_3417_, 3);
v___x_3441_ = l_Lean_Name_mkStr4(v___x_3412_, v___x_3413_, v___y_3417_, v___x_3440_);
lean_inc_n(v___x_3439_, 13);
v___x_3442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3439_);
lean_ctor_set(v___x_3442_, 1, v___x_3440_);
v___x_3443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_3444_ = l_Lean_Name_mkStr4(v___x_3412_, v___x_3413_, v___y_3417_, v___x_3443_);
v___x_3445_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_3446_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_3447_ = lean_array_size(v___y_3420_);
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_3447_, v___x_3448_, v___y_3420_);
v___x_3450_ = l_Array_append___redArg(v___x_3446_, v___x_3449_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3439_);
lean_ctor_set(v___x_3451_, 1, v___x_3445_);
lean_ctor_set(v___x_3451_, 2, v___x_3450_);
v___x_3452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3439_);
lean_ctor_set(v___x_3452_, 1, v___x_3445_);
lean_ctor_set(v___x_3452_, 2, v___x_3446_);
v___x_3453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_3454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3439_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
lean_inc_ref(v___x_3452_);
v___x_3455_ = l_Lean_Syntax_node4(v___x_3439_, v___x_3444_, v___x_3451_, v___x_3452_, v___x_3454_, v_val_3434_);
v___x_3456_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3441_, v___x_3442_, v___x_3455_);
v___x_3457_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2));
v___x_3458_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_3459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3439_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
lean_inc(v___y_3415_);
lean_inc(v___y_3418_);
v___x_3461_ = l_Lean_Syntax_node2(v___x_3439_, v___y_3418_, v___x_3460_, v___y_3415_);
v___x_3462_ = l_Lean_Syntax_node1(v___x_3439_, v___x_3445_, v___x_3461_);
v___x_3463_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3458_, v___x_3452_, v___x_3462_);
v___x_3464_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4));
v___x_3465_ = l_Lean_Name_mkStr4(v___x_3412_, v___x_3413_, v___y_3417_, v___x_3464_);
v___x_3466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_3467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3439_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
lean_inc(v___x_3456_);
v___x_3468_ = l_Lean_Syntax_node2(v___x_3439_, v___x_3465_, v___x_3467_, v___x_3456_);
v___x_3469_ = l_Lean_Syntax_node1(v___x_3439_, v___x_3445_, v___x_3468_);
lean_inc(v_val_3423_);
lean_inc(v_mods_3411_);
v___x_3470_ = l_Lean_Syntax_node4(v___x_3439_, v___x_3457_, v_mods_3411_, v_val_3423_, v___x_3463_, v___x_3469_);
v___x_3471_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_3421_);
lean_dec_ref(v___y_3421_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3470_);
v___x_3473_ = v___x_3436_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3470_);
v___x_3473_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3474_, 0, v_stx_3395_);
lean_ctor_set(v___x_3474_, 1, v_mods_3411_);
lean_ctor_set(v___x_3474_, 2, v_val_3423_);
lean_ctor_set(v___x_3474_, 3, v___x_3471_);
lean_ctor_set(v___x_3474_, 4, v___y_3415_);
lean_ctor_set(v___x_3474_, 5, v___x_3456_);
lean_ctor_set(v___x_3474_, 6, v___x_3473_);
lean_ctor_set_uint8(v___x_3474_, sizeof(void*)*7, v___x_3438_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___y_3416_);
return v___x_3475_;
}
}
}
else
{
lean_object* v___x_3479_; 
lean_dec(v_val_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3415_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 5, v_ref_3433_);
v___x_3479_ = v___x_3431_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_methods_3424_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_quotContext_3425_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_currMacroScope_3426_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_currRecDepth_3427_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v_maxRecDepth_3428_);
lean_ctor_set(v_reuseFailAlloc_3482_, 5, v_ref_3433_);
v___x_3479_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5));
v___x_3481_ = l_Lean_Macro_throwError___redArg(v___x_3480_, v___x_3479_, v___y_3416_);
lean_dec_ref(v___x_3479_);
return v___x_3481_;
}
}
}
}
v___jp_3484_:
{
lean_object* v_bs_3494_; lean_object* v___x_3495_; 
v_bs_3494_ = l_Lean_Syntax_getArgs(v___y_3490_);
lean_dec(v___y_3490_);
v___x_3495_ = l_Lake_expandBinders(v_bs_3494_, v___y_3492_, v___y_3493_);
lean_dec_ref(v_bs_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_a_3497_; lean_object* v_ids_3498_; lean_object* v___x_3499_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
v_a_3497_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3495_, 2);
v_ids_3498_ = l_Lean_Syntax_getArgs(v___y_3489_);
lean_dec(v___y_3489_);
v___x_3499_ = l_Lake_mkDepArrow(v_a_3496_, v___y_3488_);
if (lean_obj_tag(v___y_3487_) == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3500_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3498_);
v___x_3501_ = lean_array_get_size(v___x_3500_);
v___x_3502_ = lean_nat_dec_lt(v___x_3410_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec_ref(v___x_3500_);
lean_dec(v___x_3499_);
lean_dec_ref(v_ids_3498_);
lean_dec(v_a_3496_);
lean_dec(v_val_x3f_3491_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v___x_3503_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6));
v___x_3504_ = l_Lean_Macro_throwError___redArg(v___x_3503_, v___y_3492_, v_a_3497_);
lean_dec_ref(v___y_3492_);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_array_fget(v___x_3500_, v___x_3410_);
lean_dec_ref(v___x_3500_);
v___y_3415_ = v___x_3499_;
v___y_3416_ = v_a_3497_;
v___y_3417_ = v___y_3485_;
v___y_3418_ = v___y_3486_;
v___y_3419_ = v___y_3492_;
v___y_3420_ = v_a_3496_;
v___y_3421_ = v_ids_3498_;
v___y_3422_ = v_val_x3f_3491_;
v_val_3423_ = v___x_3505_;
goto v___jp_3414_;
}
}
else
{
lean_object* v_val_3506_; 
v_val_3506_ = lean_ctor_get(v___y_3487_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v___y_3487_, 1);
v___y_3415_ = v___x_3499_;
v___y_3416_ = v_a_3497_;
v___y_3417_ = v___y_3485_;
v___y_3418_ = v___y_3486_;
v___y_3419_ = v___y_3492_;
v___y_3420_ = v_a_3496_;
v___y_3421_ = v_ids_3498_;
v___y_3422_ = v_val_x3f_3491_;
v_val_3423_ = v_val_3506_;
goto v___jp_3414_;
}
}
else
{
lean_object* v_a_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___y_3492_);
lean_dec(v_val_x3f_3491_);
lean_dec(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec(v_mods_3411_);
lean_dec(v_stx_3395_);
v_a_3507_ = lean_ctor_get(v___x_3495_, 0);
v_a_3508_ = lean_ctor_get(v___x_3495_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3495_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_inc(v_a_3507_);
lean_dec(v___x_3495_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3507_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___boxed(lean_object* v_stx_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_stx_3559_, v_a_3560_, v_a_3561_);
lean_dec_ref(v_a_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(lean_object* v_typeName_3564_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3565_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0));
v___x_3566_ = l_Lean_Name_getString_x21(v_typeName_3564_);
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = lean_box(0);
v___x_3569_ = l_Lean_Name_str___override(v___x_3568_, v___x_3567_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___boxed(lean_object* v_typeName_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_typeName_3570_);
lean_dec(v_typeName_3570_);
return v_res_3571_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3582_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6);
v___x_3583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3584_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_3585_ = l_Lean_Syntax_node7(v___x_3584_, v___x_3583_, v___x_3582_, v___x_3582_, v___x_3582_, v___x_3582_, v___x_3582_, v___x_3582_, v___x_3582_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(lean_object* v_stx_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_methods_3591_; lean_object* v_quotContext_3592_; lean_object* v_currMacroScope_3593_; lean_object* v_currRecDepth_3594_; lean_object* v_maxRecDepth_3595_; lean_object* v_ref_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v_id_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_ref_3627_; lean_object* v___x_3628_; 
v_methods_3591_ = lean_ctor_get(v_a_3589_, 0);
v_quotContext_3592_ = lean_ctor_get(v_a_3589_, 1);
v_currMacroScope_3593_ = lean_ctor_get(v_a_3589_, 2);
v_currRecDepth_3594_ = lean_ctor_get(v_a_3589_, 3);
v_maxRecDepth_3595_ = lean_ctor_get(v_a_3589_, 4);
v_ref_3596_ = lean_ctor_get(v_a_3589_, 5);
v___x_3597_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1));
lean_inc(v_stx_3588_);
v___x_3598_ = l_Lean_Syntax_isOfKind(v_stx_3588_, v___x_3597_);
v_ref_3627_ = l_Lean_replaceRef(v_stx_3588_, v_ref_3596_);
lean_inc(v_maxRecDepth_3595_);
lean_inc(v_currRecDepth_3594_);
lean_inc(v_currMacroScope_3593_);
lean_inc(v_quotContext_3592_);
lean_inc(v_methods_3591_);
v___x_3628_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3628_, 0, v_methods_3591_);
lean_ctor_set(v___x_3628_, 1, v_quotContext_3592_);
lean_ctor_set(v___x_3628_, 2, v_currMacroScope_3593_);
lean_ctor_set(v___x_3628_, 3, v_currRecDepth_3594_);
lean_ctor_set(v___x_3628_, 4, v_maxRecDepth_3595_);
lean_ctor_set(v___x_3628_, 5, v_ref_3627_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec(v_stx_3588_);
v___x_3629_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3630_ = l_Lean_Macro_throwError___redArg(v___x_3629_, v___x_3628_, v_a_3590_);
lean_dec_ref_known(v___x_3628_, 6);
return v___x_3630_;
}
else
{
lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_typeId_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___x_3654_; lean_object* v_id_x3f_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3654_ = lean_unsigned_to_nat(0u);
v___x_3694_ = l_Lean_Syntax_getArg(v_stx_3588_, v___x_3654_);
v___x_3695_ = l_Lean_Syntax_isNone(v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3694_);
v___x_3697_ = l_Lean_Syntax_matchesNull(v___x_3694_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v___x_3694_);
lean_dec(v_stx_3588_);
v___x_3698_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3699_ = l_Lean_Macro_throwError___redArg(v___x_3698_, v___x_3628_, v_a_3590_);
lean_dec_ref_known(v___x_3628_, 6);
return v___x_3699_;
}
else
{
lean_object* v_id_x3f_3700_; lean_object* v___x_3701_; 
v_id_x3f_3700_ = l_Lean_Syntax_getArg(v___x_3694_, v___x_3654_);
lean_dec(v___x_3694_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_id_x3f_3700_);
v_id_x3f_3656_ = v___x_3701_;
v___y_3657_ = v___x_3628_;
v___y_3658_ = v_a_3590_;
goto v___jp_3655_;
}
}
else
{
lean_object* v___x_3702_; 
lean_dec(v___x_3694_);
v___x_3702_ = lean_box(0);
v_id_x3f_3656_ = v___x_3702_;
v___y_3657_ = v___x_3628_;
v___y_3658_ = v_a_3590_;
goto v___jp_3655_;
}
v___jp_3631_:
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = l_Lean_TSyntax_getId(v_typeId_3634_);
v___x_3638_ = l_Lean_Name_hasMacroScopes(v___x_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v___x_3637_);
lean_dec(v___x_3637_);
v___y_3619_ = v___y_3635_;
v___y_3620_ = v___y_3632_;
v___y_3621_ = v_typeId_3634_;
v___y_3622_ = v___y_3636_;
v___y_3623_ = v___y_3633_;
v___y_3624_ = v___x_3639_;
goto v___jp_3618_;
}
else
{
lean_object* v_view_3640_; lean_object* v_name_3641_; lean_object* v_imported_3642_; lean_object* v_ctx_3643_; lean_object* v_scopes_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3653_; 
v_view_3640_ = l_Lean_extractMacroScopes(v___x_3637_);
v_name_3641_ = lean_ctor_get(v_view_3640_, 0);
v_imported_3642_ = lean_ctor_get(v_view_3640_, 1);
v_ctx_3643_ = lean_ctor_get(v_view_3640_, 2);
v_scopes_3644_ = lean_ctor_get(v_view_3640_, 3);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_view_3640_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3646_ = v_view_3640_;
v_isShared_3647_ = v_isSharedCheck_3653_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_scopes_3644_);
lean_inc(v_ctx_3643_);
lean_inc(v_imported_3642_);
lean_inc(v_name_3641_);
lean_dec(v_view_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3653_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_name_3641_);
lean_dec(v_name_3641_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3648_);
v___x_3650_ = v___x_3646_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_imported_3642_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_ctx_3643_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_scopes_3644_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_MacroScopesView_review(v___x_3650_);
v___y_3619_ = v___y_3635_;
v___y_3620_ = v___y_3632_;
v___y_3621_ = v_typeId_3634_;
v___y_3622_ = v___y_3636_;
v___y_3623_ = v___y_3633_;
v___y_3624_ = v___x_3651_;
goto v___jp_3618_;
}
}
}
}
v___jp_3655_:
{
lean_object* v___x_3659_; lean_object* v_id_3660_; 
v___x_3659_ = lean_unsigned_to_nat(1u);
v_id_3660_ = l_Lean_Syntax_getArg(v_stx_3588_, v___x_3659_);
if (lean_obj_tag(v_id_x3f_3656_) == 1)
{
lean_object* v_val_3661_; 
v_val_3661_ = lean_ctor_get(v_id_x3f_3656_, 0);
lean_inc(v_val_3661_);
lean_dec_ref_known(v_id_x3f_3656_, 1);
v___y_3600_ = v___x_3659_;
v___y_3601_ = v_id_3660_;
v_id_3602_ = v_val_3661_;
v___y_3603_ = v___y_3657_;
v___y_3604_ = v___y_3658_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
lean_dec(v_id_x3f_3656_);
v___x_3662_ = ((lean_object*)(l_Lake_configField___closed__13));
lean_inc(v_id_3660_);
v___x_3663_ = l_Lean_Syntax_isOfKind(v_id_3660_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
lean_inc(v_id_3660_);
v___x_3665_ = l_Lean_Syntax_isOfKind(v_id_3660_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3667_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3660_, v___x_3666_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v_a_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
v_a_3669_ = lean_ctor_get(v___x_3667_, 1);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3667_, 2);
v___y_3632_ = v___x_3659_;
v___y_3633_ = v_id_3660_;
v_typeId_3634_ = v_a_3668_;
v___y_3635_ = v___y_3657_;
v___y_3636_ = v_a_3669_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3670_; lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v_id_3660_);
lean_dec_ref(v___y_3657_);
lean_dec(v_stx_3588_);
v_a_3670_ = lean_ctor_get(v___x_3667_, 0);
v_a_3671_ = lean_ctor_get(v___x_3667_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3667_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_inc(v_a_3670_);
lean_dec(v___x_3667_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3670_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_id_3679_; uint8_t v___x_3680_; 
v_id_3679_ = l_Lean_Syntax_getArg(v_id_3660_, v___x_3654_);
lean_inc(v_id_3679_);
v___x_3680_ = l_Lean_Syntax_isOfKind(v_id_3679_, v___x_3662_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec(v_id_3679_);
v___x_3681_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3682_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3660_, v___x_3681_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_a_3684_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
v_a_3684_ = lean_ctor_get(v___x_3682_, 1);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3682_, 2);
v___y_3632_ = v___x_3659_;
v___y_3633_ = v_id_3660_;
v_typeId_3634_ = v_a_3683_;
v___y_3635_ = v___y_3657_;
v___y_3636_ = v_a_3684_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3685_; lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_id_3660_);
lean_dec_ref(v___y_3657_);
lean_dec(v_stx_3588_);
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
v___y_3632_ = v___x_3659_;
v___y_3633_ = v_id_3660_;
v_typeId_3634_ = v_id_3679_;
v___y_3635_ = v___y_3657_;
v___y_3636_ = v___y_3658_;
goto v___jp_3631_;
}
}
}
else
{
lean_inc(v_id_3660_);
v___y_3632_ = v___x_3659_;
v___y_3633_ = v_id_3660_;
v_typeId_3634_ = v_id_3660_;
v___y_3635_ = v___y_3657_;
v___y_3636_ = v___y_3658_;
goto v___jp_3631_;
}
}
}
}
v___jp_3599_:
{
lean_object* v_ref_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_ref_3605_ = lean_ctor_get(v___y_3603_, 5);
lean_inc(v_ref_3605_);
lean_dec_ref(v___y_3603_);
v___x_3606_ = 0;
v___x_3607_ = l_Lean_SourceInfo_fromRef(v_ref_3605_, v___x_3606_);
lean_dec(v_ref_3605_);
v___x_3608_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3));
v___x_3609_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4));
lean_inc(v___x_3607_);
v___x_3610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3607_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3608_, v___x_3610_);
v___x_3612_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___y_3600_);
lean_inc(v_id_3602_);
v___x_3614_ = lean_array_push(v___x_3613_, v_id_3602_);
v___x_3615_ = lean_box(0);
v___x_3616_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3616_, 0, v_stx_3588_);
lean_ctor_set(v___x_3616_, 1, v___x_3612_);
lean_ctor_set(v___x_3616_, 2, v_id_3602_);
lean_ctor_set(v___x_3616_, 3, v___x_3614_);
lean_ctor_set(v___x_3616_, 4, v___y_3601_);
lean_ctor_set(v___x_3616_, 5, v___x_3611_);
lean_ctor_set(v___x_3616_, 6, v___x_3615_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*7, v___x_3598_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v___y_3604_);
return v___x_3617_;
}
v___jp_3618_:
{
uint8_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = 0;
v___x_3626_ = l_Lean_mkIdentFrom(v___y_3621_, v___y_3624_, v___x_3625_);
lean_dec(v___y_3621_);
v___y_3600_ = v___y_3620_;
v___y_3601_ = v___y_3623_;
v_id_3602_ = v___x_3626_;
v___y_3603_ = v___y_3619_;
v___y_3604_ = v___y_3622_;
goto v___jp_3599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___boxed(lean_object* v_stx_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v_stx_3703_, v_a_3704_, v_a_3705_);
lean_dec_ref(v_a_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__0(lean_object* v_x_3707_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___x_3709_ = lean_array_push(v___x_3708_, v_x_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__1(lean_object* v_00___3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_bs_3714_){
_start:
{
uint8_t v___x_3715_; 
v___x_3715_ = lean_usize_dec_lt(v_i_3713_, v_sz_3712_);
if (v___x_3715_ == 0)
{
return v_bs_3714_;
}
else
{
lean_object* v_v_3716_; lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; size_t v___x_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v_v_3716_ = lean_array_uget(v_bs_3714_, v_i_3713_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3714_, v_i_3713_, v___x_3717_);
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3713_, v___x_3719_);
v___x_3721_ = lean_array_uset(v_bs_x27_3718_, v_i_3713_, v_v_3716_);
v_i_3713_ = v___x_3720_;
v_bs_3714_ = v___x_3721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3___boxed(lean_object* v_sz_3723_, lean_object* v_i_3724_, lean_object* v_bs_3725_){
_start:
{
size_t v_sz_boxed_3726_; size_t v_i_boxed_3727_; lean_object* v_res_3728_; 
v_sz_boxed_3726_ = lean_unbox_usize(v_sz_3723_);
lean_dec(v_sz_3723_);
v_i_boxed_3727_ = lean_unbox_usize(v_i_3724_);
lean_dec(v_i_3724_);
v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_boxed_3726_, v_i_boxed_3727_, v_bs_3725_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(size_t v_sz_3729_, size_t v_i_3730_, lean_object* v_bs_3731_){
_start:
{
uint8_t v___x_3732_; 
v___x_3732_ = lean_usize_dec_lt(v_i_3730_, v_sz_3729_);
if (v___x_3732_ == 0)
{
return v_bs_3731_;
}
else
{
lean_object* v_v_3733_; lean_object* v___x_3734_; lean_object* v_bs_x27_3735_; size_t v___x_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v_v_3733_ = lean_array_uget(v_bs_3731_, v_i_3730_);
v___x_3734_ = lean_unsigned_to_nat(0u);
v_bs_x27_3735_ = lean_array_uset(v_bs_3731_, v_i_3730_, v___x_3734_);
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3730_, v___x_3736_);
v___x_3738_ = lean_array_uset(v_bs_x27_3735_, v_i_3730_, v_v_3733_);
v_i_3730_ = v___x_3737_;
v_bs_3731_ = v___x_3738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6___boxed(lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_bs_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_boxed_3743_, v_i_boxed_3744_, v_bs_3742_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_bs_3748_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_usize_dec_lt(v_i_3747_, v_sz_3746_);
if (v___x_3749_ == 0)
{
return v_bs_3748_;
}
else
{
lean_object* v_v_3750_; lean_object* v___x_3751_; lean_object* v_bs_x27_3752_; size_t v___x_3753_; size_t v___x_3754_; lean_object* v___x_3755_; 
v_v_3750_ = lean_array_uget(v_bs_3748_, v_i_3747_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v_bs_x27_3752_ = lean_array_uset(v_bs_3748_, v_i_3747_, v___x_3751_);
v___x_3753_ = ((size_t)1ULL);
v___x_3754_ = lean_usize_add(v_i_3747_, v___x_3753_);
v___x_3755_ = lean_array_uset(v_bs_x27_3752_, v_i_3747_, v_v_3750_);
v_i_3747_ = v___x_3754_;
v_bs_3748_ = v___x_3755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5___boxed(lean_object* v_sz_3757_, lean_object* v_i_3758_, lean_object* v_bs_3759_){
_start:
{
size_t v_sz_boxed_3760_; size_t v_i_boxed_3761_; lean_object* v_res_3762_; 
v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3757_);
lean_dec(v_sz_3757_);
v_i_boxed_3761_ = lean_unbox_usize(v_i_3758_);
lean_dec(v_i_3758_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_boxed_3760_, v_i_boxed_3761_, v_bs_3759_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(lean_object* v_as_3763_, size_t v_i_3764_, size_t v_stop_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
uint8_t v___x_3769_; 
v___x_3769_ = lean_usize_dec_eq(v_i_3764_, v_stop_3765_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_array_uget_borrowed(v_as_3763_, v_i_3764_);
lean_inc(v___x_3770_);
v___x_3771_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v___x_3770_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v_a_3773_; lean_object* v___x_3774_; size_t v___x_3775_; size_t v___x_3776_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
v_a_3773_ = lean_ctor_get(v___x_3771_, 1);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3771_, 2);
v___x_3774_ = lean_array_push(v_b_3766_, v_a_3772_);
v___x_3775_ = ((size_t)1ULL);
v___x_3776_ = lean_usize_add(v_i_3764_, v___x_3775_);
v_i_3764_ = v___x_3776_;
v_b_3766_ = v___x_3774_;
v___y_3768_ = v_a_3773_;
goto _start;
}
else
{
lean_object* v_a_3778_; lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_b_3766_);
v_a_3778_ = lean_ctor_get(v___x_3771_, 0);
v_a_3779_ = lean_ctor_get(v___x_3771_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3771_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_inc(v_a_3778_);
lean_dec(v___x_3771_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3778_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3787_, 0, v_b_3766_);
lean_ctor_set(v___x_3787_, 1, v___y_3768_);
return v___x_3787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8___boxed(lean_object* v_as_3788_, lean_object* v_i_3789_, lean_object* v_stop_3790_, lean_object* v_b_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
size_t v_i_boxed_3794_; size_t v_stop_boxed_3795_; lean_object* v_res_3796_; 
v_i_boxed_3794_ = lean_unbox_usize(v_i_3789_);
lean_dec(v_i_3789_);
v_stop_boxed_3795_ = lean_unbox_usize(v_stop_3790_);
lean_dec(v_stop_3790_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v_as_3788_, v_i_boxed_3794_, v_stop_boxed_3795_, v_b_3791_, v___y_3792_, v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec_ref(v_as_3788_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(lean_object* v_as_3797_, size_t v_i_3798_, size_t v_stop_3799_, lean_object* v_b_3800_){
_start:
{
lean_object* v___y_3802_; uint8_t v___x_3806_; 
v___x_3806_ = lean_usize_dec_eq(v_i_3798_, v_stop_3799_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; lean_object* v_decl_x3f_3808_; 
v___x_3807_ = lean_array_uget_borrowed(v_as_3797_, v_i_3798_);
v_decl_x3f_3808_ = lean_ctor_get(v___x_3807_, 6);
if (lean_obj_tag(v_decl_x3f_3808_) == 0)
{
v___y_3802_ = v_b_3800_;
goto v___jp_3801_;
}
else
{
lean_object* v_val_3809_; lean_object* v___x_3810_; 
v_val_3809_ = lean_ctor_get(v_decl_x3f_3808_, 0);
lean_inc(v_val_3809_);
v___x_3810_ = lean_array_push(v_b_3800_, v_val_3809_);
v___y_3802_ = v___x_3810_;
goto v___jp_3801_;
}
}
else
{
return v_b_3800_;
}
v___jp_3801_:
{
size_t v___x_3803_; size_t v___x_3804_; 
v___x_3803_ = ((size_t)1ULL);
v___x_3804_ = lean_usize_add(v_i_3798_, v___x_3803_);
v_i_3798_ = v___x_3804_;
v_b_3800_ = v___y_3802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2___boxed(lean_object* v_as_3811_, lean_object* v_i_3812_, lean_object* v_stop_3813_, lean_object* v_b_3814_){
_start:
{
size_t v_i_boxed_3815_; size_t v_stop_boxed_3816_; lean_object* v_res_3817_; 
v_i_boxed_3815_ = lean_unbox_usize(v_i_3812_);
lean_dec(v_i_3812_);
v_stop_boxed_3816_ = lean_unbox_usize(v_stop_3813_);
lean_dec(v_stop_3813_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3811_, v_i_boxed_3815_, v_stop_boxed_3816_, v_b_3814_);
lean_dec_ref(v_as_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(lean_object* v_as_3818_, lean_object* v_start_3819_, lean_object* v_stop_3820_){
_start:
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___x_3822_ = lean_nat_dec_lt(v_start_3819_, v_stop_3820_);
if (v___x_3822_ == 0)
{
return v___x_3821_;
}
else
{
lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3823_ = lean_array_get_size(v_as_3818_);
v___x_3824_ = lean_nat_dec_le(v_stop_3820_, v___x_3823_);
if (v___x_3824_ == 0)
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_nat_dec_lt(v_start_3819_, v___x_3823_);
if (v___x_3825_ == 0)
{
return v___x_3821_;
}
else
{
size_t v___x_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v___x_3826_ = lean_usize_of_nat(v_start_3819_);
v___x_3827_ = lean_usize_of_nat(v___x_3823_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3818_, v___x_3826_, v___x_3827_, v___x_3821_);
return v___x_3828_;
}
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_usize_of_nat(v_start_3819_);
v___x_3830_ = lean_usize_of_nat(v_stop_3820_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3818_, v___x_3829_, v___x_3830_, v___x_3821_);
return v___x_3831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2___boxed(lean_object* v_as_3832_, lean_object* v_start_3833_, lean_object* v_stop_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_as_3832_, v_start_3833_, v_stop_3834_);
lean_dec(v_stop_3834_);
lean_dec(v_start_3833_);
lean_dec_ref(v_as_3832_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_bs_3838_){
_start:
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3839_ == 0)
{
return v_bs_3838_;
}
else
{
lean_object* v_v_3840_; lean_object* v___x_3841_; lean_object* v_bs_x27_3842_; size_t v___x_3843_; size_t v___x_3844_; lean_object* v___x_3845_; 
v_v_3840_ = lean_array_uget(v_bs_3838_, v_i_3837_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v_bs_x27_3842_ = lean_array_uset(v_bs_3838_, v_i_3837_, v___x_3841_);
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3837_, v___x_3843_);
v___x_3845_ = lean_array_uset(v_bs_x27_3842_, v_i_3837_, v_v_3840_);
v_i_3837_ = v___x_3844_;
v_bs_3838_ = v___x_3845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7___boxed(lean_object* v_sz_3847_, lean_object* v_i_3848_, lean_object* v_bs_3849_){
_start:
{
size_t v_sz_boxed_3850_; size_t v_i_boxed_3851_; lean_object* v_res_3852_; 
v_sz_boxed_3850_ = lean_unbox_usize(v_sz_3847_);
lean_dec(v_sz_3847_);
v_i_boxed_3851_ = lean_unbox_usize(v_i_3848_);
lean_dec(v_i_3848_);
v_res_3852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_boxed_3850_, v_i_boxed_3851_, v_bs_3849_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(size_t v_sz_3853_, size_t v_i_3854_, lean_object* v_bs_3855_){
_start:
{
uint8_t v___x_3856_; 
v___x_3856_ = lean_usize_dec_lt(v_i_3854_, v_sz_3853_);
if (v___x_3856_ == 0)
{
return v_bs_3855_;
}
else
{
lean_object* v_v_3857_; lean_object* v___x_3858_; lean_object* v_bs_x27_3859_; lean_object* v___x_3860_; size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v_v_3857_ = lean_array_uget(v_bs_3855_, v_i_3854_);
v___x_3858_ = lean_unsigned_to_nat(0u);
v_bs_x27_3859_ = lean_array_uset(v_bs_3855_, v_i_3854_, v___x_3858_);
v___x_3860_ = l_Lake_BinderSyntaxView_mkArgument(v_v_3857_);
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3854_, v___x_3861_);
v___x_3863_ = lean_array_uset(v_bs_x27_3859_, v_i_3854_, v___x_3860_);
v_i_3854_ = v___x_3862_;
v_bs_3855_ = v___x_3863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0___boxed(lean_object* v_sz_3865_, lean_object* v_i_3866_, lean_object* v_bs_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3865_);
lean_dec(v_sz_3865_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3866_);
lean_dec(v_i_3866_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_boxed_3868_, v_i_boxed_3869_, v_bs_3867_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(size_t v_sz_3871_, size_t v_i_3872_, lean_object* v_bs_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_usize_dec_lt(v_i_3872_, v_sz_3871_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v_bs_3873_);
lean_ctor_set(v___x_3877_, 1, v___y_3875_);
return v___x_3877_;
}
else
{
lean_object* v_v_3878_; lean_object* v___x_3879_; 
v_v_3878_ = lean_array_uget_borrowed(v_bs_3873_, v_i_3872_);
lean_inc(v_v_3878_);
v___x_3879_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_v_3878_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_a_3881_; lean_object* v___x_3882_; lean_object* v_bs_x27_3883_; size_t v___x_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
v_a_3881_ = lean_ctor_get(v___x_3879_, 1);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3879_, 2);
v___x_3882_ = lean_unsigned_to_nat(0u);
v_bs_x27_3883_ = lean_array_uset(v_bs_3873_, v_i_3872_, v___x_3882_);
v___x_3884_ = ((size_t)1ULL);
v___x_3885_ = lean_usize_add(v_i_3872_, v___x_3884_);
v___x_3886_ = lean_array_uset(v_bs_x27_3883_, v_i_3872_, v_a_3880_);
v_i_3872_ = v___x_3885_;
v_bs_3873_ = v___x_3886_;
v___y_3875_ = v_a_3881_;
goto _start;
}
else
{
lean_object* v_a_3888_; lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_bs_3873_);
v_a_3888_ = lean_ctor_get(v___x_3879_, 0);
v_a_3889_ = lean_ctor_get(v___x_3879_, 1);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3879_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_inc(v_a_3888_);
lean_dec(v___x_3879_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3888_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1___boxed(lean_object* v_sz_3897_, lean_object* v_i_3898_, lean_object* v_bs_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3897_);
lean_dec(v_sz_3897_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3898_);
lean_dec(v_i_3898_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_boxed_3902_, v_i_boxed_3903_, v_bs_3899_, v___y_3900_, v___y_3901_);
lean_dec_ref(v___y_3900_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(size_t v_sz_3905_, size_t v_i_3906_, lean_object* v_bs_3907_){
_start:
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_usize_dec_lt(v_i_3906_, v_sz_3905_);
if (v___x_3908_ == 0)
{
return v_bs_3907_;
}
else
{
lean_object* v_v_3909_; lean_object* v___x_3910_; lean_object* v_bs_x27_3911_; size_t v___x_3912_; size_t v___x_3913_; lean_object* v___x_3914_; 
v_v_3909_ = lean_array_uget(v_bs_3907_, v_i_3906_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v_bs_x27_3911_ = lean_array_uset(v_bs_3907_, v_i_3906_, v___x_3910_);
v___x_3912_ = ((size_t)1ULL);
v___x_3913_ = lean_usize_add(v_i_3906_, v___x_3912_);
v___x_3914_ = lean_array_uset(v_bs_x27_3911_, v_i_3906_, v_v_3909_);
v_i_3906_ = v___x_3913_;
v_bs_3907_ = v___x_3914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4___boxed(lean_object* v_sz_3916_, lean_object* v_i_3917_, lean_object* v_bs_3918_){
_start:
{
size_t v_sz_boxed_3919_; size_t v_i_boxed_3920_; lean_object* v_res_3921_; 
v_sz_boxed_3919_ = lean_unbox_usize(v_sz_3916_);
lean_dec(v_sz_3916_);
v_i_boxed_3920_ = lean_unbox_usize(v_i_3917_);
lean_dec(v_i_3917_);
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_boxed_3919_, v_i_boxed_3920_, v_bs_3918_);
return v_res_3921_;
}
}
static lean_object* _init_l_Lake_expandConfigDecl___closed__3(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = l_Lake_expandConfigDecl___lam__1(v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl(lean_object* v_stx_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = ((lean_object*)(l_Lake_configDecl___closed__1));
lean_inc(v_stx_3943_);
v___x_3947_ = l_Lean_Syntax_isOfKind(v_stx_3943_, v___x_3946_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_stx_3943_);
v___x_3948_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3949_ = l_Lean_Macro_throwError___redArg(v___x_3948_, v_a_3944_, v_a_3945_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3950_ = lean_unsigned_to_nat(0u);
v___x_3951_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_3950_);
v___x_3952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v___x_3951_);
v___x_3953_ = l_Lean_Syntax_isOfKind(v___x_3951_, v___x_3952_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_3954_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3955_ = l_Lean_Macro_throwError___redArg(v___x_3954_, v_a_3944_, v_a_3945_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v_tk_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; size_t v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; size_t v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; size_t v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; size_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; size_t v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; size_t v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v_a_4159_; lean_object* v_a_4160_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; size_t v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; size_t v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v_ctor_x3f_4250_; lean_object* v_fs_x3f_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v_ctor_x3f_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4297_; lean_object* v_ps_x3f_4298_; lean_object* v_xty_x3f_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v_xty_x3f_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v_ty_x3f_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_3956_ = lean_unsigned_to_nat(1u);
v_tk_3992_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_3956_);
v___x_3993_ = lean_unsigned_to_nat(2u);
v___x_3994_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_3993_);
v___x_4244_ = lean_unsigned_to_nat(3u);
v___x_4245_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_4244_);
v___x_4356_ = lean_unsigned_to_nat(4u);
v___x_4357_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_4356_);
v___x_4358_ = l_Lean_Syntax_isNone(v___x_4357_);
if (v___x_4358_ == 0)
{
uint8_t v___x_4359_; 
lean_inc(v___x_4357_);
v___x_4359_ = l_Lean_Syntax_matchesNull(v___x_4357_, v___x_3956_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_dec(v___x_4357_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4360_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4361_ = l_Lean_Macro_throwError___redArg(v___x_4360_, v_a_3944_, v_a_3945_);
return v___x_4361_;
}
else
{
lean_object* v_ty_x3f_4362_; lean_object* v___x_4363_; 
v_ty_x3f_4362_ = l_Lean_Syntax_getArg(v___x_4357_, v___x_3950_);
lean_dec(v___x_4357_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v_ty_x3f_4362_);
v_ty_x3f_4332_ = v___x_4363_;
v___y_4333_ = v_a_3944_;
v___y_4334_ = v_a_3945_;
goto v___jp_4331_;
}
}
else
{
lean_object* v___x_4364_; 
lean_dec(v___x_4357_);
v___x_4364_ = lean_box(0);
v_ty_x3f_4332_ = v___x_4364_;
v___y_4333_ = v_a_3944_;
v___y_4334_ = v_a_3945_;
goto v___jp_4331_;
}
v___jp_3957_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_array_get_size(v___y_3965_);
lean_dec_ref(v___y_3965_);
v___x_3968_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v___y_3966_, v___y_3959_, v___x_3967_, v___y_3961_, v___y_3960_, v___y_3963_, v___y_3962_);
lean_dec_ref(v___y_3963_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3982_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_a_3970_ = lean_ctor_get(v___x_3968_, 1);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3972_ = v___x_3968_;
v_isShared_3973_ = v_isSharedCheck_3982_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3982_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3974_ = lean_mk_empty_array_with_capacity(v___x_3956_);
v___x_3975_ = lean_array_push(v___x_3974_, v___y_3958_);
v___x_3976_ = l_Array_append___redArg(v___x_3975_, v_a_3969_);
lean_dec(v_a_3969_);
v___x_3977_ = lean_box(2);
lean_inc(v___y_3964_);
v___x_3978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set(v___x_3978_, 1, v___y_3964_);
lean_ctor_set(v___x_3978_, 2, v___x_3976_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3978_);
v___x_3980_ = v___x_3972_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_a_3970_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v___y_3958_);
v_a_3983_ = lean_ctor_get(v___x_3968_, 0);
v_a_3984_ = lean_ctor_get(v___x_3968_, 1);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3968_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_inc(v_a_3983_);
lean_dec(v___x_3968_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3983_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
v___jp_3995_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; size_t v_sz_4018_; lean_object* v___x_4019_; size_t v_sz_4020_; lean_object* v___x_4021_; size_t v_sz_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_inc_ref(v___y_3997_);
v___x_4015_ = l_Array_append___redArg(v___y_3997_, v___y_4014_);
lean_dec_ref(v___y_4014_);
lean_inc_n(v___y_4012_, 3);
lean_inc_n(v___y_4008_, 5);
v___x_4016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4016_, 0, v___y_4008_);
lean_ctor_set(v___x_4016_, 1, v___y_4012_);
lean_ctor_set(v___x_4016_, 2, v___x_4015_);
v___x_4017_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__2));
v_sz_4018_ = lean_array_size(v___y_4005_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_4018_, v___y_4000_, v___y_4005_);
v_sz_4020_ = lean_array_size(v___x_4019_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_4020_, v___y_4000_, v___x_4019_);
v_sz_4022_ = lean_array_size(v___x_4021_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_4022_, v___y_4000_, v___x_4021_);
v___x_4024_ = l_Array_append___redArg(v___y_3997_, v___x_4023_);
lean_dec_ref(v___x_4023_);
v___x_4025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4025_, 0, v___y_4008_);
lean_ctor_set(v___x_4025_, 1, v___y_4012_);
lean_ctor_set(v___x_4025_, 2, v___x_4024_);
v___x_4026_ = l_Lean_Syntax_node1(v___y_4008_, v___x_4017_, v___x_4025_);
v___x_4027_ = l_Lean_Syntax_node3(v___y_4008_, v___y_4012_, v___y_3998_, v___x_4016_, v___x_4026_);
lean_inc(v___y_3996_);
v___x_4028_ = l_Lean_Syntax_node6(v___y_4008_, v___y_3996_, v___y_4010_, v___x_3994_, v___y_4001_, v___y_4006_, v___x_4027_, v___y_4009_);
lean_inc(v___x_3951_);
lean_inc(v___y_4007_);
v___x_4029_ = l_Lean_Syntax_node2(v___y_4008_, v___y_4007_, v___x_3951_, v___x_4028_);
v___x_4030_ = l_Lean_Syntax_getArg(v___x_3951_, v___x_3993_);
lean_dec(v___x_3951_);
v___x_4031_ = l_Lean_Syntax_getOptional_x3f(v___x_4030_);
lean_dec(v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_box(0);
v___y_3958_ = v___x_4029_;
v___y_3959_ = v___y_4002_;
v___y_3960_ = v___y_4003_;
v___y_3961_ = v___y_4004_;
v___y_3962_ = v___y_3999_;
v___y_3963_ = v___y_4011_;
v___y_3964_ = v___y_4012_;
v___y_3965_ = v___y_4013_;
v___y_3966_ = v___x_4032_;
goto v___jp_3957_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
v_val_4033_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4031_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_val_4033_);
lean_dec(v___x_4031_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_val_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
v___y_3958_ = v___x_4029_;
v___y_3959_ = v___y_4002_;
v___y_3960_ = v___y_4003_;
v___y_3961_ = v___y_4004_;
v___y_3962_ = v___y_3999_;
v___y_3963_ = v___y_4011_;
v___y_3964_ = v___y_4012_;
v___y_3965_ = v___y_4013_;
v___y_3966_ = v___x_4038_;
goto v___jp_3957_;
}
}
}
}
v___jp_4041_:
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_3996_ = v___y_4042_;
v___y_3997_ = v___y_4043_;
v___y_3998_ = v___y_4044_;
v___y_3999_ = v___y_4045_;
v___y_4000_ = v___y_4046_;
v___y_4001_ = v___y_4047_;
v___y_4002_ = v___y_4048_;
v___y_4003_ = v___y_4049_;
v___y_4004_ = v___y_4050_;
v___y_4005_ = v___y_4051_;
v___y_4006_ = v___y_4052_;
v___y_4007_ = v___y_4053_;
v___y_4008_ = v___y_4054_;
v___y_4009_ = v___y_4055_;
v___y_4010_ = v___y_4056_;
v___y_4011_ = v___y_4057_;
v___y_4012_ = v___y_4058_;
v___y_4013_ = v___y_4059_;
v___y_4014_ = v___x_4060_;
goto v___jp_3995_;
}
v___jp_4061_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_inc_ref(v___y_4064_);
v___x_4083_ = l_Array_append___redArg(v___y_4064_, v___y_4082_);
lean_dec_ref(v___y_4082_);
lean_inc_n(v___y_4079_, 2);
lean_inc_n(v___y_4074_, 4);
v___x_4084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4084_, 0, v___y_4074_);
lean_ctor_set(v___x_4084_, 1, v___y_4079_);
lean_ctor_set(v___x_4084_, 2, v___x_4083_);
lean_inc(v___y_4081_);
v___x_4085_ = l_Lean_Syntax_node3(v___y_4074_, v___y_4081_, v___y_4076_, v___y_4070_, v___x_4084_);
v___x_4086_ = l_Lean_Syntax_node1(v___y_4074_, v___y_4079_, v___x_4085_);
v___x_4087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_4088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___y_4074_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
if (lean_obj_tag(v___y_4063_) == 0)
{
v___y_4042_ = v___y_4062_;
v___y_4043_ = v___y_4064_;
v___y_4044_ = v___x_4088_;
v___y_4045_ = v___y_4065_;
v___y_4046_ = v___y_4066_;
v___y_4047_ = v___y_4067_;
v___y_4048_ = v___y_4068_;
v___y_4049_ = v___y_4069_;
v___y_4050_ = v___y_4071_;
v___y_4051_ = v___y_4072_;
v___y_4052_ = v___x_4086_;
v___y_4053_ = v___y_4073_;
v___y_4054_ = v___y_4074_;
v___y_4055_ = v___y_4075_;
v___y_4056_ = v___y_4077_;
v___y_4057_ = v___y_4078_;
v___y_4058_ = v___y_4079_;
v___y_4059_ = v___y_4080_;
goto v___jp_4041_;
}
else
{
lean_object* v_val_4089_; 
v_val_4089_ = lean_ctor_get(v___y_4063_, 0);
lean_inc(v_val_4089_);
lean_dec_ref_known(v___y_4063_, 1);
if (lean_obj_tag(v_val_4089_) == 0)
{
v___y_4042_ = v___y_4062_;
v___y_4043_ = v___y_4064_;
v___y_4044_ = v___x_4088_;
v___y_4045_ = v___y_4065_;
v___y_4046_ = v___y_4066_;
v___y_4047_ = v___y_4067_;
v___y_4048_ = v___y_4068_;
v___y_4049_ = v___y_4069_;
v___y_4050_ = v___y_4071_;
v___y_4051_ = v___y_4072_;
v___y_4052_ = v___x_4086_;
v___y_4053_ = v___y_4073_;
v___y_4054_ = v___y_4074_;
v___y_4055_ = v___y_4075_;
v___y_4056_ = v___y_4077_;
v___y_4057_ = v___y_4078_;
v___y_4058_ = v___y_4079_;
v___y_4059_ = v___y_4080_;
goto v___jp_4041_;
}
else
{
lean_object* v_val_4090_; lean_object* v___x_4091_; 
v_val_4090_ = lean_ctor_get(v_val_4089_, 0);
lean_inc(v_val_4090_);
lean_dec_ref_known(v_val_4089_, 1);
v___x_4091_ = l_Lake_expandConfigDecl___lam__0(v_val_4090_);
v___y_3996_ = v___y_4062_;
v___y_3997_ = v___y_4064_;
v___y_3998_ = v___x_4088_;
v___y_3999_ = v___y_4065_;
v___y_4000_ = v___y_4066_;
v___y_4001_ = v___y_4067_;
v___y_4002_ = v___y_4068_;
v___y_4003_ = v___y_4069_;
v___y_4004_ = v___y_4071_;
v___y_4005_ = v___y_4072_;
v___y_4006_ = v___x_4086_;
v___y_4007_ = v___y_4073_;
v___y_4008_ = v___y_4074_;
v___y_4009_ = v___y_4075_;
v___y_4010_ = v___y_4077_;
v___y_4011_ = v___y_4078_;
v___y_4012_ = v___y_4079_;
v___y_4013_ = v___y_4080_;
v___y_4014_ = v___x_4091_;
goto v___jp_3995_;
}
}
}
v___jp_4092_:
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_4062_ = v___y_4093_;
v___y_4063_ = v___y_4094_;
v___y_4064_ = v___y_4095_;
v___y_4065_ = v___y_4096_;
v___y_4066_ = v___y_4097_;
v___y_4067_ = v___y_4098_;
v___y_4068_ = v___y_4099_;
v___y_4069_ = v___y_4100_;
v___y_4070_ = v___y_4101_;
v___y_4071_ = v___y_4102_;
v___y_4072_ = v___y_4103_;
v___y_4073_ = v___y_4104_;
v___y_4074_ = v___y_4105_;
v___y_4075_ = v___y_4107_;
v___y_4076_ = v___y_4106_;
v___y_4077_ = v___y_4108_;
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4110_;
v___y_4080_ = v___y_4112_;
v___y_4081_ = v___y_4111_;
v___y_4082_ = v___x_4113_;
goto v___jp_4061_;
}
v___jp_4114_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_inc_ref_n(v___y_4118_, 2);
v___x_4136_ = l_Array_append___redArg(v___y_4118_, v___y_4135_);
lean_dec_ref(v___y_4135_);
lean_inc_n(v___y_4133_, 2);
lean_inc_n(v___y_4128_, 4);
v___x_4137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4137_, 0, v___y_4128_);
lean_ctor_set(v___x_4137_, 1, v___y_4133_);
lean_ctor_set(v___x_4137_, 2, v___x_4136_);
lean_inc(v___y_4131_);
v___x_4138_ = l_Lean_Syntax_node2(v___y_4128_, v___y_4131_, v___y_4125_, v___x_4137_);
v___x_4139_ = ((lean_object*)(l_Lake_configDecl___closed__32));
v___x_4140_ = ((lean_object*)(l_Lake_configDecl___closed__33));
v___x_4141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___y_4128_);
lean_ctor_set(v___x_4141_, 1, v___x_4139_);
v___x_4142_ = l_Array_append___redArg(v___y_4118_, v___y_4121_);
lean_dec_ref(v___y_4121_);
v___x_4143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4143_, 0, v___y_4128_);
lean_ctor_set(v___x_4143_, 1, v___y_4133_);
lean_ctor_set(v___x_4143_, 2, v___x_4142_);
if (lean_obj_tag(v___y_4117_) == 0)
{
v___y_4093_ = v___y_4115_;
v___y_4094_ = v___y_4116_;
v___y_4095_ = v___y_4118_;
v___y_4096_ = v___y_4119_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___x_4138_;
v___y_4099_ = v___y_4122_;
v___y_4100_ = v___y_4123_;
v___y_4101_ = v___x_4143_;
v___y_4102_ = v___y_4124_;
v___y_4103_ = v___y_4126_;
v___y_4104_ = v___y_4127_;
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___x_4141_;
v___y_4107_ = v___y_4129_;
v___y_4108_ = v___y_4130_;
v___y_4109_ = v___y_4132_;
v___y_4110_ = v___y_4133_;
v___y_4111_ = v___x_4140_;
v___y_4112_ = v___y_4134_;
goto v___jp_4092_;
}
else
{
lean_object* v_val_4144_; 
v_val_4144_ = lean_ctor_get(v___y_4117_, 0);
lean_inc(v_val_4144_);
lean_dec_ref_known(v___y_4117_, 1);
if (lean_obj_tag(v_val_4144_) == 0)
{
v___y_4093_ = v___y_4115_;
v___y_4094_ = v___y_4116_;
v___y_4095_ = v___y_4118_;
v___y_4096_ = v___y_4119_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___x_4138_;
v___y_4099_ = v___y_4122_;
v___y_4100_ = v___y_4123_;
v___y_4101_ = v___x_4143_;
v___y_4102_ = v___y_4124_;
v___y_4103_ = v___y_4126_;
v___y_4104_ = v___y_4127_;
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___x_4141_;
v___y_4107_ = v___y_4129_;
v___y_4108_ = v___y_4130_;
v___y_4109_ = v___y_4132_;
v___y_4110_ = v___y_4133_;
v___y_4111_ = v___x_4140_;
v___y_4112_ = v___y_4134_;
goto v___jp_4092_;
}
else
{
lean_object* v_val_4145_; lean_object* v___x_4146_; 
v_val_4145_ = lean_ctor_get(v_val_4144_, 0);
lean_inc(v_val_4145_);
lean_dec_ref_known(v_val_4144_, 1);
v___x_4146_ = l_Lake_expandConfigDecl___lam__0(v_val_4145_);
v___y_4062_ = v___y_4115_;
v___y_4063_ = v___y_4116_;
v___y_4064_ = v___y_4118_;
v___y_4065_ = v___y_4119_;
v___y_4066_ = v___y_4120_;
v___y_4067_ = v___x_4138_;
v___y_4068_ = v___y_4122_;
v___y_4069_ = v___y_4123_;
v___y_4070_ = v___x_4143_;
v___y_4071_ = v___y_4124_;
v___y_4072_ = v___y_4126_;
v___y_4073_ = v___y_4127_;
v___y_4074_ = v___y_4128_;
v___y_4075_ = v___y_4129_;
v___y_4076_ = v___x_4141_;
v___y_4077_ = v___y_4130_;
v___y_4078_ = v___y_4132_;
v___y_4079_ = v___y_4133_;
v___y_4080_ = v___y_4134_;
v___y_4081_ = v___x_4140_;
v___y_4082_ = v___x_4146_;
goto v___jp_4061_;
}
}
}
v___jp_4147_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; size_t v_sz_4174_; lean_object* v___x_4175_; size_t v_sz_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4161_ = lean_array_get_size(v_a_4159_);
v___x_4162_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_a_4159_, v___x_3950_, v___x_4161_);
v___x_4163_ = 0;
v___x_4164_ = l_Lean_SourceInfo_fromRef(v___y_4153_, v___x_4163_);
lean_dec(v___y_4153_);
v___x_4165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_4166_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__4));
v___x_4167_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__5));
v___x_4168_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__7));
lean_inc_n(v___x_4164_, 3);
v___x_4169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4164_);
lean_ctor_set(v___x_4169_, 1, v___x_4166_);
v___x_4170_ = l_Lean_Syntax_node1(v___x_4164_, v___x_4168_, v___x_4169_);
v___x_4171_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_4172_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_4173_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_4174_ = lean_array_size(v___y_4158_);
lean_inc_ref(v___y_4158_);
v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_4174_, v___y_4154_, v___y_4158_);
v_sz_4176_ = lean_array_size(v___x_4175_);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_4176_, v___y_4154_, v___x_4175_);
v___x_4178_ = l_Array_append___redArg(v___x_4173_, v___x_4177_);
lean_dec_ref(v___x_4177_);
v___x_4179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4164_);
lean_ctor_set(v___x_4179_, 1, v___x_4172_);
lean_ctor_set(v___x_4179_, 2, v___x_4178_);
if (lean_obj_tag(v___y_4152_) == 1)
{
lean_object* v_val_4180_; lean_object* v___x_4181_; 
v_val_4180_ = lean_ctor_get(v___y_4152_, 0);
lean_inc(v_val_4180_);
lean_dec_ref_known(v___y_4152_, 1);
v___x_4181_ = l_Array_mkArray1___redArg(v_val_4180_);
v___y_4115_ = v___x_4167_;
v___y_4116_ = v___y_4150_;
v___y_4117_ = v___y_4151_;
v___y_4118_ = v___x_4173_;
v___y_4119_ = v_a_4160_;
v___y_4120_ = v___y_4154_;
v___y_4121_ = v___y_4157_;
v___y_4122_ = v___y_4148_;
v___y_4123_ = v_a_4159_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___x_4179_;
v___y_4126_ = v___x_4162_;
v___y_4127_ = v___x_4165_;
v___y_4128_ = v___x_4164_;
v___y_4129_ = v___y_4155_;
v___y_4130_ = v___x_4170_;
v___y_4131_ = v___x_4171_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___x_4172_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___x_4181_;
goto v___jp_4114_;
}
else
{
lean_object* v___x_4182_; 
lean_dec(v___y_4152_);
v___x_4182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_4115_ = v___x_4167_;
v___y_4116_ = v___y_4150_;
v___y_4117_ = v___y_4151_;
v___y_4118_ = v___x_4173_;
v___y_4119_ = v_a_4160_;
v___y_4120_ = v___y_4154_;
v___y_4121_ = v___y_4157_;
v___y_4122_ = v___y_4148_;
v___y_4123_ = v_a_4159_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___x_4179_;
v___y_4126_ = v___x_4162_;
v___y_4127_ = v___x_4165_;
v___y_4128_ = v___x_4164_;
v___y_4129_ = v___y_4155_;
v___y_4130_ = v___x_4170_;
v___y_4131_ = v___x_4171_;
v___y_4132_ = v___y_4156_;
v___y_4133_ = v___x_4172_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___x_4182_;
goto v___jp_4114_;
}
}
v___jp_4183_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4197_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_4196_);
v___x_4198_ = lean_array_get_size(v___x_4197_);
v___x_4199_ = lean_nat_dec_lt(v___x_3950_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_dec_ref(v___x_4197_);
v___y_4148_ = v___y_4184_;
v___y_4149_ = v___y_4185_;
v___y_4150_ = v___y_4186_;
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___y_4190_;
v___y_4153_ = v___y_4191_;
v___y_4154_ = v___y_4192_;
v___y_4155_ = v___y_4193_;
v___y_4156_ = v___y_4194_;
v___y_4157_ = v___y_4196_;
v___y_4158_ = v___y_4195_;
v_a_4159_ = v___y_4187_;
v_a_4160_ = v___y_4189_;
goto v___jp_4147_;
}
else
{
size_t v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_usize_of_nat(v___x_4198_);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v___x_4197_, v___y_4192_, v___x_4200_, v___y_4187_, v___y_4194_, v___y_4189_);
lean_dec_ref(v___x_4197_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v_a_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
v_a_4203_ = lean_ctor_get(v___x_4201_, 1);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4201_, 2);
v___y_4148_ = v___y_4184_;
v___y_4149_ = v___y_4185_;
v___y_4150_ = v___y_4186_;
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___y_4190_;
v___y_4153_ = v___y_4191_;
v___y_4154_ = v___y_4192_;
v___y_4155_ = v___y_4193_;
v___y_4156_ = v___y_4194_;
v___y_4157_ = v___y_4196_;
v___y_4158_ = v___y_4195_;
v_a_4159_ = v_a_4202_;
v_a_4160_ = v_a_4203_;
goto v___jp_4147_;
}
else
{
lean_object* v_a_4204_; lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec(v___y_4188_);
lean_dec(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec(v___x_3994_);
lean_dec(v___x_3951_);
v_a_4204_ = lean_ctor_get(v___x_4201_, 0);
v_a_4205_ = lean_ctor_get(v___x_4201_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4201_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_inc(v_a_4204_);
lean_dec(v___x_4201_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4204_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
v___jp_4213_:
{
size_t v_sz_4227_; lean_object* v___x_4228_; 
v_sz_4227_ = lean_array_size(v___y_4226_);
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_4227_, v___y_4221_, v___y_4226_, v___y_4224_, v___y_4217_);
if (lean_obj_tag(v___x_4228_) == 0)
{
if (lean_obj_tag(v___y_4223_) == 0)
{
lean_object* v_a_4229_; lean_object* v_a_4230_; lean_object* v___x_4231_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
v_a_4230_ = lean_ctor_get(v___x_4228_, 1);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4228_, 2);
v___x_4231_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4184_ = v___y_4214_;
v___y_4185_ = v___y_4215_;
v___y_4186_ = v___y_4216_;
v___y_4187_ = v_a_4229_;
v___y_4188_ = v___y_4218_;
v___y_4189_ = v_a_4230_;
v___y_4190_ = v___y_4219_;
v___y_4191_ = v___y_4220_;
v___y_4192_ = v___y_4221_;
v___y_4193_ = v___y_4222_;
v___y_4194_ = v___y_4224_;
v___y_4195_ = v___y_4225_;
v___y_4196_ = v___x_4231_;
goto v___jp_4183_;
}
else
{
lean_object* v_a_4232_; lean_object* v_a_4233_; lean_object* v_val_4234_; 
v_a_4232_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4232_);
v_a_4233_ = lean_ctor_get(v___x_4228_, 1);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4228_, 2);
v_val_4234_ = lean_ctor_get(v___y_4223_, 0);
lean_inc(v_val_4234_);
lean_dec_ref_known(v___y_4223_, 1);
v___y_4184_ = v___y_4214_;
v___y_4185_ = v___y_4215_;
v___y_4186_ = v___y_4216_;
v___y_4187_ = v_a_4232_;
v___y_4188_ = v___y_4218_;
v___y_4189_ = v_a_4233_;
v___y_4190_ = v___y_4219_;
v___y_4191_ = v___y_4220_;
v___y_4192_ = v___y_4221_;
v___y_4193_ = v___y_4222_;
v___y_4194_ = v___y_4224_;
v___y_4195_ = v___y_4225_;
v___y_4196_ = v_val_4234_;
goto v___jp_4183_;
}
}
else
{
lean_object* v_a_4235_; lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec(v___x_3994_);
lean_dec(v___x_3951_);
v_a_4235_ = lean_ctor_get(v___x_4228_, 0);
v_a_4236_ = lean_ctor_get(v___x_4228_, 1);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4228_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_inc(v_a_4235_);
lean_dec(v___x_4228_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4235_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
v___jp_4246_:
{
lean_object* v_methods_4254_; lean_object* v_quotContext_4255_; lean_object* v_currMacroScope_4256_; lean_object* v_currRecDepth_4257_; lean_object* v_maxRecDepth_4258_; lean_object* v_ref_4259_; lean_object* v_bs_4260_; lean_object* v_ref_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_methods_4254_ = lean_ctor_get(v___y_4252_, 0);
v_quotContext_4255_ = lean_ctor_get(v___y_4252_, 1);
v_currMacroScope_4256_ = lean_ctor_get(v___y_4252_, 2);
v_currRecDepth_4257_ = lean_ctor_get(v___y_4252_, 3);
v_maxRecDepth_4258_ = lean_ctor_get(v___y_4252_, 4);
v_ref_4259_ = lean_ctor_get(v___y_4252_, 5);
v_bs_4260_ = l_Lean_Syntax_getArgs(v___x_4245_);
lean_dec(v___x_4245_);
v_ref_4261_ = l_Lean_replaceRef(v_tk_3992_, v_ref_4259_);
lean_dec(v_tk_3992_);
lean_inc(v_ref_4261_);
lean_inc(v_maxRecDepth_4258_);
lean_inc(v_currRecDepth_4257_);
lean_inc(v_currMacroScope_4256_);
lean_inc(v_quotContext_4255_);
lean_inc(v_methods_4254_);
v___x_4262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4262_, 0, v_methods_4254_);
lean_ctor_set(v___x_4262_, 1, v_quotContext_4255_);
lean_ctor_set(v___x_4262_, 2, v_currMacroScope_4256_);
lean_ctor_set(v___x_4262_, 3, v_currRecDepth_4257_);
lean_ctor_set(v___x_4262_, 4, v_maxRecDepth_4258_);
lean_ctor_set(v___x_4262_, 5, v_ref_4261_);
v___x_4263_ = l_Lake_expandBinders(v_bs_4260_, v___x_4262_, v___y_4253_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; size_t v_sz_4269_; size_t v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
v_a_4265_ = lean_ctor_get(v___x_4263_, 1);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4263_, 2);
v___x_4266_ = lean_unsigned_to_nat(7u);
v___x_4267_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_4266_);
lean_dec(v_stx_3943_);
v___x_4268_ = l_Lean_Syntax_getArg(v___x_3994_, v___x_3950_);
v_sz_4269_ = lean_array_size(v_a_4264_);
v___x_4270_ = ((size_t)0ULL);
v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_4269_, v___x_4270_, v_a_4264_);
lean_inc(v___x_4268_);
v___x_4272_ = l_Lean_Syntax_mkApp(v___x_4268_, v___x_4271_);
if (lean_obj_tag(v_fs_x3f_4251_) == 0)
{
lean_object* v___x_4273_; 
v___x_4273_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4214_ = v___x_4268_;
v___y_4215_ = v___x_4272_;
v___y_4216_ = v_ctor_x3f_4250_;
v___y_4217_ = v_a_4265_;
v___y_4218_ = v___y_4247_;
v___y_4219_ = v___y_4248_;
v___y_4220_ = v_ref_4261_;
v___y_4221_ = v___x_4270_;
v___y_4222_ = v___x_4267_;
v___y_4223_ = v___y_4249_;
v___y_4224_ = v___x_4262_;
v___y_4225_ = v_bs_4260_;
v___y_4226_ = v___x_4273_;
goto v___jp_4213_;
}
else
{
lean_object* v_val_4274_; 
v_val_4274_ = lean_ctor_get(v_fs_x3f_4251_, 0);
lean_inc(v_val_4274_);
lean_dec_ref_known(v_fs_x3f_4251_, 1);
v___y_4214_ = v___x_4268_;
v___y_4215_ = v___x_4272_;
v___y_4216_ = v_ctor_x3f_4250_;
v___y_4217_ = v_a_4265_;
v___y_4218_ = v___y_4247_;
v___y_4219_ = v___y_4248_;
v___y_4220_ = v_ref_4261_;
v___y_4221_ = v___x_4270_;
v___y_4222_ = v___x_4267_;
v___y_4223_ = v___y_4249_;
v___y_4224_ = v___x_4262_;
v___y_4225_ = v_bs_4260_;
v___y_4226_ = v_val_4274_;
goto v___jp_4213_;
}
}
else
{
lean_object* v_a_4275_; lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref_known(v___x_4262_, 6);
lean_dec(v_ref_4261_);
lean_dec_ref(v_bs_4260_);
lean_dec(v_fs_x3f_4251_);
lean_dec(v_ctor_x3f_4250_);
lean_dec(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___x_3994_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v_a_4275_ = lean_ctor_get(v___x_4263_, 0);
v_a_4276_ = lean_ctor_get(v___x_4263_, 1);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4263_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_inc(v_a_4275_);
lean_dec(v___x_4263_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4275_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
v___jp_4284_:
{
lean_object* v___x_4292_; lean_object* v_fs_x3f_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4292_ = l_Lean_Syntax_getArg(v___y_4288_, v___x_3993_);
lean_dec(v___y_4288_);
v_fs_x3f_4293_ = l_Lean_Syntax_getArgs(v___x_4292_);
lean_dec(v___x_4292_);
v___x_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4294_, 0, v_ctor_x3f_4289_);
v___x_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4295_, 0, v_fs_x3f_4293_);
v___y_4247_ = v___y_4285_;
v___y_4248_ = v___y_4286_;
v___y_4249_ = v___y_4287_;
v_ctor_x3f_4250_ = v___x_4294_;
v_fs_x3f_4251_ = v___x_4295_;
v___y_4252_ = v___y_4290_;
v___y_4253_ = v___y_4291_;
goto v___jp_4246_;
}
v___jp_4296_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4302_ = lean_unsigned_to_nat(6u);
v___x_4303_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_4302_);
v___x_4304_ = l_Lean_Syntax_isNone(v___x_4303_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
lean_inc(v___x_4303_);
v___x_4305_ = l_Lean_Syntax_matchesNull(v___x_4303_, v___x_4244_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_dec(v___x_4303_);
lean_dec(v_xty_x3f_4299_);
lean_dec(v_ps_x3f_4298_);
lean_dec(v___y_4297_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4306_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4307_ = l_Lean_Macro_throwError___redArg(v___x_4306_, v___y_4300_, v___y_4301_);
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = l_Lean_Syntax_getArg(v___x_4303_, v___x_3950_);
v___x_4309_ = ((lean_object*)(l_Lake_configDecl___closed__45));
v___x_4310_ = l_Lean_Syntax_isOfKind(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
lean_dec(v___x_4303_);
lean_dec(v_xty_x3f_4299_);
lean_dec(v_ps_x3f_4298_);
lean_dec(v___y_4297_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4311_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4312_ = l_Lean_Macro_throwError___redArg(v___x_4311_, v___y_4300_, v___y_4301_);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; uint8_t v___x_4314_; 
v___x_4313_ = l_Lean_Syntax_getArg(v___x_4303_, v___x_3956_);
v___x_4314_ = l_Lean_Syntax_isNone(v___x_4313_);
if (v___x_4314_ == 0)
{
uint8_t v___x_4315_; 
lean_inc(v___x_4313_);
v___x_4315_ = l_Lean_Syntax_matchesNull(v___x_4313_, v___x_3956_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_dec(v___x_4313_);
lean_dec(v___x_4303_);
lean_dec(v_xty_x3f_4299_);
lean_dec(v_ps_x3f_4298_);
lean_dec(v___y_4297_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4316_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4317_ = l_Lean_Macro_throwError___redArg(v___x_4316_, v___y_4300_, v___y_4301_);
return v___x_4317_;
}
else
{
lean_object* v_ctor_x3f_4318_; lean_object* v___x_4319_; 
v_ctor_x3f_4318_ = l_Lean_Syntax_getArg(v___x_4313_, v___x_3950_);
lean_dec(v___x_4313_);
v___x_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4319_, 0, v_ctor_x3f_4318_);
v___y_4285_ = v_xty_x3f_4299_;
v___y_4286_ = v___y_4297_;
v___y_4287_ = v_ps_x3f_4298_;
v___y_4288_ = v___x_4303_;
v_ctor_x3f_4289_ = v___x_4319_;
v___y_4290_ = v___y_4300_;
v___y_4291_ = v___y_4301_;
goto v___jp_4284_;
}
}
else
{
lean_object* v___x_4320_; 
lean_dec(v___x_4313_);
v___x_4320_ = lean_box(0);
v___y_4285_ = v_xty_x3f_4299_;
v___y_4286_ = v___y_4297_;
v___y_4287_ = v_ps_x3f_4298_;
v___y_4288_ = v___x_4303_;
v_ctor_x3f_4289_ = v___x_4320_;
v___y_4290_ = v___y_4300_;
v___y_4291_ = v___y_4301_;
goto v___jp_4284_;
}
}
}
}
else
{
lean_object* v___x_4321_; 
lean_dec(v___x_4303_);
v___x_4321_ = lean_box(0);
v___y_4247_ = v_xty_x3f_4299_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v_ps_x3f_4298_;
v_ctor_x3f_4250_ = v___x_4321_;
v_fs_x3f_4251_ = v___x_4321_;
v___y_4252_ = v___y_4300_;
v___y_4253_ = v___y_4301_;
goto v___jp_4246_;
}
}
v___jp_4322_:
{
lean_object* v_ps_x3f_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_ps_x3f_4328_ = l_Lean_Syntax_getArgs(v___y_4324_);
lean_dec(v___y_4324_);
v___x_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4329_, 0, v_ps_x3f_4328_);
v___x_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4330_, 0, v_xty_x3f_4325_);
v___y_4297_ = v___y_4323_;
v_ps_x3f_4298_ = v___x_4329_;
v_xty_x3f_4299_ = v___x_4330_;
v___y_4300_ = v___y_4326_;
v___y_4301_ = v___y_4327_;
goto v___jp_4296_;
}
v___jp_4331_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4335_ = lean_unsigned_to_nat(5u);
v___x_4336_ = l_Lean_Syntax_getArg(v_stx_3943_, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_isNone(v___x_4336_);
if (v___x_4337_ == 0)
{
uint8_t v___x_4338_; 
lean_inc(v___x_4336_);
v___x_4338_ = l_Lean_Syntax_matchesNull(v___x_4336_, v___x_3956_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_dec(v___x_4336_);
lean_dec(v_ty_x3f_4332_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4339_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4340_ = l_Lean_Macro_throwError___redArg(v___x_4339_, v___y_4333_, v___y_4334_);
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4341_ = l_Lean_Syntax_getArg(v___x_4336_, v___x_3950_);
lean_dec(v___x_4336_);
v___x_4342_ = ((lean_object*)(l_Lake_configDecl___closed__33));
lean_inc(v___x_4341_);
v___x_4343_ = l_Lean_Syntax_isOfKind(v___x_4341_, v___x_4342_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_dec(v___x_4341_);
lean_dec(v_ty_x3f_4332_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4344_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4345_ = l_Lean_Macro_throwError___redArg(v___x_4344_, v___y_4333_, v___y_4334_);
return v___x_4345_;
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4346_ = l_Lean_Syntax_getArg(v___x_4341_, v___x_3956_);
v___x_4347_ = l_Lean_Syntax_getArg(v___x_4341_, v___x_3993_);
lean_dec(v___x_4341_);
v___x_4348_ = l_Lean_Syntax_isNone(v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
lean_inc(v___x_4347_);
v___x_4349_ = l_Lean_Syntax_matchesNull(v___x_4347_, v___x_3956_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec(v___x_4347_);
lean_dec(v___x_4346_);
lean_dec(v_ty_x3f_4332_);
lean_dec(v___x_4245_);
lean_dec(v___x_3994_);
lean_dec(v_tk_3992_);
lean_dec(v___x_3951_);
lean_dec(v_stx_3943_);
v___x_4350_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4351_ = l_Lean_Macro_throwError___redArg(v___x_4350_, v___y_4333_, v___y_4334_);
return v___x_4351_;
}
else
{
lean_object* v_xty_x3f_4352_; lean_object* v___x_4353_; 
v_xty_x3f_4352_ = l_Lean_Syntax_getArg(v___x_4347_, v___x_3950_);
lean_dec(v___x_4347_);
v___x_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4353_, 0, v_xty_x3f_4352_);
v___y_4323_ = v_ty_x3f_4332_;
v___y_4324_ = v___x_4346_;
v_xty_x3f_4325_ = v___x_4353_;
v___y_4326_ = v___y_4333_;
v___y_4327_ = v___y_4334_;
goto v___jp_4322_;
}
}
else
{
lean_object* v___x_4354_; 
lean_dec(v___x_4347_);
v___x_4354_ = lean_box(0);
v___y_4323_ = v_ty_x3f_4332_;
v___y_4324_ = v___x_4346_;
v_xty_x3f_4325_ = v___x_4354_;
v___y_4326_ = v___y_4333_;
v___y_4327_ = v___y_4334_;
goto v___jp_4322_;
}
}
}
}
else
{
lean_object* v___x_4355_; 
lean_dec(v___x_4336_);
v___x_4355_ = lean_box(0);
v___y_4297_ = v_ty_x3f_4332_;
v_ps_x3f_4298_ = v___x_4355_;
v_xty_x3f_4299_ = v___x_4355_;
v___y_4300_ = v___y_4333_;
v___y_4301_ = v___y_4334_;
goto v___jp_4296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___boxed(lean_object* v_stx_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lake_expandConfigDecl(v_stx_4365_, v_a_4366_, v_a_4367_);
lean_dec_ref(v_a_4366_);
return v_res_4368_;
}
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
