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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(lean_object* v_a_332_, lean_object* v___x_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_bs_336_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_332_ = stack[0].m_obj;
lean_object* v___x_333_ = stack[1].m_obj;
size_t v_sz_334_ = stack[2].m_num;
size_t v_i_335_ = stack[3].m_num;
lean_object* v_bs_336_ = stack[4].m_obj;
lean_object* v_res_349_;
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_332_, v___x_333_, v_sz_334_, v_i_335_, v_bs_336_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___boxed(lean_object* v_a_350_, lean_object* v___x_351_, lean_object* v_sz_352_, lean_object* v_i_353_, lean_object* v_bs_354_){
_start:
{
size_t v_sz_boxed_355_; size_t v_i_boxed_356_; lean_object* v_res_357_; 
v_sz_boxed_355_ = lean_unbox_usize(v_sz_352_);
lean_dec(v_sz_352_);
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_350_, v___x_351_, v_sz_boxed_355_, v_i_boxed_356_, v_bs_354_);
return v_res_357_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(uint8_t v___x_358_, lean_object* v_____do__lift_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_SourceInfo_fromRef(v_____do__lift_359_, v___x_358_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_358_ = stack[0].m_num;
lean_object* v_____do__lift_359_ = stack[1].m_obj;
lean_object* v___y_360_ = stack[2].m_obj;
lean_object* v___y_361_ = stack[3].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_358_, v_____do__lift_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1___boxed(lean_object* v___x_365_, lean_object* v_____do__lift_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v___x_78989__boxed_369_; lean_object* v_res_370_; 
v___x_78989__boxed_369_ = lean_unbox(v___x_365_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_78989__boxed_369_, v_____do__lift_366_, v___y_367_, v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_____do__lift_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(lean_object* v_structId_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = l_Lean_TSyntax_getId(v_structId_372_);
v___x_375_ = l_Lean_Name_append(v___x_374_, v_x_373_);
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___closed__0));
v___x_377_ = l_Lean_Name_str___override(v___x_375_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0___boxed(lean_object* v_structId_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_378_, v_x_379_);
lean_dec(v_structId_378_);
return v_res_380_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_388_ = l_String_toRawSubstring_x27(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__22));
v___x_416_ = l_String_toRawSubstring_x27(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__28));
v___x_424_ = l_String_toRawSubstring_x27(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__32));
v___x_430_ = l_String_toRawSubstring_x27(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__35));
v___x_435_ = l_String_toRawSubstring_x27(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__40));
v___x_444_ = l_Lean_mkCIdent(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_448_ = l_String_toRawSubstring_x27(v___x_447_);
return v___x_448_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(lean_object* v_structTy_479_, lean_object* v_type_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_vis_x3f_483_, lean_object* v_structId_484_, lean_object* v_as_485_, size_t v_i_486_, size_t v_stop_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_eq(v_i_486_, v_stop_487_);
if (v___x_491_ == 0)
{
lean_object* v_cmds_492_; lean_object* v_fields_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_703_; 
v_cmds_492_ = lean_ctor_get(v_b_488_, 0);
v_fields_493_ = lean_ctor_get(v_b_488_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_488_);
if (v_isSharedCheck_703_ == 0)
{
v___x_495_ = v_b_488_;
v_isShared_496_ = v_isSharedCheck_703_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_fields_493_);
lean_inc(v_cmds_492_);
lean_dec(v_b_488_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_703_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_656_; uint8_t v___x_687_; 
v___x_497_ = lean_array_uget_borrowed(v_as_485_, v_i_486_);
v___x_498_ = l_Lean_TSyntax_getId(v___x_497_);
lean_inc(v___x_498_);
lean_inc(v___x_497_);
v___x_499_ = l_Lake_Name_quoteFrom(v___x_497_, v___x_498_, v___x_491_);
v___x_687_ = l_Lean_Name_hasMacroScopes(v___x_498_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_484_, v___x_498_);
v___y_656_ = v___x_688_;
goto v___jp_655_;
}
else
{
lean_object* v_view_689_; lean_object* v_name_690_; lean_object* v_imported_691_; lean_object* v_ctx_692_; lean_object* v_scopes_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_view_689_ = l_Lean_extractMacroScopes(v___x_498_);
v_name_690_ = lean_ctor_get(v_view_689_, 0);
v_imported_691_ = lean_ctor_get(v_view_689_, 1);
v_ctx_692_ = lean_ctor_get(v_view_689_, 2);
v_scopes_693_ = lean_ctor_get(v_view_689_, 3);
v_isSharedCheck_702_ = !lean_is_exclusive(v_view_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v_view_689_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_scopes_693_);
lean_inc(v_ctx_692_);
lean_inc(v_imported_691_);
lean_inc(v_name_690_);
lean_dec(v_view_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_484_, v_name_690_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_imported_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_ctx_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_scopes_693_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_MacroScopesView_review(v___x_699_);
v___y_656_ = v___x_700_;
goto v___jp_655_;
}
}
}
v___jp_500_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_ref_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_ref(v___y_511_);
v___x_519_ = l_Array_append___redArg(v___y_511_, v___y_518_);
lean_dec_ref(v___y_518_);
lean_inc_n(v___y_506_, 4);
lean_inc_n(v___y_504_, 18);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___y_504_);
lean_ctor_set(v___x_520_, 1, v___y_506_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
lean_inc_n(v___y_501_, 11);
lean_inc(v___y_517_);
v___x_521_ = l_Lean_Syntax_node7(v___y_504_, v___y_517_, v___y_501_, v___y_501_, v___x_520_, v___y_501_, v___y_501_, v___y_501_, v___y_501_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_515_, 4);
lean_inc_ref_n(v___y_509_, 9);
lean_inc_ref_n(v___y_516_, 9);
v___x_523_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___y_515_, v___x_522_);
v___x_524_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_526_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_525_);
v___x_527_ = l_Lean_Syntax_node1(v___y_504_, v___x_526_, v___y_501_);
v___x_528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_504_);
lean_ctor_set(v___x_528_, 1, v___x_522_);
v___x_529_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_530_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___y_515_, v___x_529_);
v___x_531_ = l_Lean_Syntax_node2(v___y_504_, v___x_530_, v___y_513_, v___y_501_);
v___x_532_ = l_Lean_Syntax_node1(v___y_504_, v___y_506_, v___x_531_);
v___x_533_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_534_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___y_515_, v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_536_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_504_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_540_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_539_);
v___x_541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_512_, 2);
lean_inc_n(v___y_505_, 2);
v___x_543_ = l_Lean_addMacroScope(v___y_505_, v___x_542_, v___y_512_);
v___x_544_ = lean_box(0);
v___x_545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_546_, 0, v___y_504_);
lean_ctor_set(v___x_546_, 1, v___x_541_);
lean_ctor_set(v___x_546_, 2, v___x_543_);
lean_ctor_set(v___x_546_, 3, v___x_545_);
lean_inc(v_type_480_);
lean_inc(v___x_499_);
lean_inc(v_structTy_479_);
v___x_547_ = l_Lean_Syntax_node3(v___y_504_, v___y_506_, v_structTy_479_, v___x_499_, v_type_480_);
v___x_548_ = l_Lean_Syntax_node2(v___y_504_, v___x_540_, v___x_546_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node2(v___y_504_, v___x_536_, v___x_538_, v___x_548_);
v___x_550_ = l_Lean_Syntax_node2(v___y_504_, v___x_534_, v___y_501_, v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_552_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___y_515_, v___x_551_);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_504_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_556_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_555_);
v___x_557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_504_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_inc(v___x_481_);
v___x_559_ = l_Lean_Syntax_node1(v___y_504_, v___y_506_, v___x_481_);
v___x_560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_561_, 0, v___y_504_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_Syntax_node3(v___y_504_, v___x_556_, v___x_558_, v___x_559_, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_565_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_563_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node2(v___y_504_, v___x_565_, v___y_501_, v___y_501_);
v_ref_567_ = l_Lean_replaceRef(v_fields_493_, v___y_503_);
lean_inc(v_ref_567_);
lean_inc(v___y_510_);
lean_inc(v___y_502_);
lean_inc(v___y_514_);
v___x_568_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_568_, 0, v___y_514_);
lean_ctor_set(v___x_568_, 1, v___y_505_);
lean_ctor_set(v___x_568_, 2, v___y_512_);
lean_ctor_set(v___x_568_, 3, v___y_502_);
lean_ctor_set(v___x_568_, 4, v___y_510_);
lean_ctor_set(v___x_568_, 5, v_ref_567_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_491_, v_ref_567_, v___x_568_, v___y_508_);
lean_dec_ref_known(v___x_568_, 6);
lean_dec(v_ref_567_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_n(v_a_570_, 30);
v_a_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_569_, 2);
lean_inc(v___y_501_);
lean_inc_n(v___y_504_, 2);
v___x_572_ = l_Lean_Syntax_node4(v___y_504_, v___x_552_, v___x_554_, v___x_562_, v___x_566_, v___y_501_);
v___x_573_ = l_Lean_Syntax_node6(v___y_504_, v___x_523_, v___x_527_, v___x_528_, v___y_501_, v___x_532_, v___x_550_, v___x_572_);
lean_inc(v___y_507_);
v___x_574_ = l_Lean_Syntax_node2(v___y_504_, v___y_507_, v___x_521_, v___x_573_);
v___x_575_ = lean_array_push(v_cmds_492_, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_509_, 7);
lean_inc_ref_n(v___y_516_, 7);
v___x_577_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_576_);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_570_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_512_, 5);
lean_inc_n(v___y_505_, 5);
v___x_582_ = l_Lean_addMacroScope(v___y_505_, v___x_581_, v___y_512_);
v___x_583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_583_, 0, v_a_570_);
lean_ctor_set(v___x_583_, 1, v___x_580_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set(v___x_583_, 3, v___x_544_);
lean_inc_ref(v___y_511_);
lean_inc_n(v___y_506_, 7);
v___x_584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_584_, 0, v_a_570_);
lean_ctor_set(v___x_584_, 1, v___y_506_);
lean_ctor_set(v___x_584_, 2, v___y_511_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_586_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v_a_570_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_590_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_592_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_591_);
v___x_593_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_594_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_593_);
v___x_595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_597_ = l_Lean_addMacroScope(v___y_505_, v___x_596_, v___y_512_);
v___x_598_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_598_, 0, v_a_570_);
lean_ctor_set(v___x_598_, 1, v___x_595_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set(v___x_598_, 3, v___x_544_);
lean_inc_ref_n(v___x_584_, 17);
lean_inc_n(v___x_594_, 2);
v___x_599_ = l_Lean_Syntax_node2(v_a_570_, v___x_594_, v___x_598_, v___x_584_);
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_601_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_600_);
v___x_602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_602_, 0, v_a_570_);
lean_ctor_set(v___x_602_, 1, v___x_553_);
lean_inc_ref_n(v___x_602_, 2);
lean_inc_n(v___x_601_, 2);
v___x_603_ = l_Lean_Syntax_node3(v_a_570_, v___x_601_, v___x_602_, v___x_584_, v___x_499_);
v___x_604_ = l_Lean_Syntax_node3(v_a_570_, v___y_506_, v___x_584_, v___x_584_, v___x_603_);
lean_inc_n(v___x_592_, 2);
v___x_605_ = l_Lean_Syntax_node2(v_a_570_, v___x_592_, v___x_599_, v___x_604_);
v___x_606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_608_ = l_Lean_addMacroScope(v___y_505_, v___x_607_, v___y_512_);
v___x_609_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_609_, 0, v_a_570_);
lean_ctor_set(v___x_609_, 1, v___x_606_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
lean_ctor_set(v___x_609_, 3, v___x_544_);
v___x_610_ = l_Lean_Syntax_node2(v_a_570_, v___x_594_, v___x_609_, v___x_584_);
lean_inc(v___x_482_);
v___x_611_ = l_Lean_Syntax_node3(v_a_570_, v___x_601_, v___x_602_, v___x_584_, v___x_482_);
v___x_612_ = l_Lean_Syntax_node3(v_a_570_, v___y_506_, v___x_584_, v___x_584_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node2(v_a_570_, v___x_592_, v___x_610_, v___x_612_);
v___x_614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_616_ = l_Lean_addMacroScope(v___y_505_, v___x_615_, v___y_512_);
v___x_617_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_617_, 0, v_a_570_);
lean_ctor_set(v___x_617_, 1, v___x_614_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_ctor_set(v___x_617_, 3, v___x_544_);
v___x_618_ = l_Lean_Syntax_node2(v_a_570_, v___x_594_, v___x_617_, v___x_584_);
v___x_619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_620_ = l_Lean_Syntax_node3(v_a_570_, v___x_601_, v___x_602_, v___x_584_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node3(v_a_570_, v___y_506_, v___x_584_, v___x_584_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node2(v_a_570_, v___x_592_, v___x_618_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node6(v_a_570_, v___y_506_, v___x_605_, v___x_584_, v___x_613_, v___x_584_, v___x_622_, v___x_584_);
v___x_624_ = l_Lean_Syntax_node1(v_a_570_, v___x_590_, v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_626_ = l_Lean_Name_mkStr4(v___y_516_, v___y_509_, v___x_524_, v___x_625_);
v___x_627_ = l_Lean_Syntax_node1(v_a_570_, v___x_626_, v___x_584_);
v___x_628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_570_);
lean_ctor_set(v___x_628_, 1, v___x_537_);
v___x_629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_631_ = l_Lean_addMacroScope(v___y_505_, v___x_630_, v___y_512_);
v___x_632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_633_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_633_, 0, v_a_570_);
lean_ctor_set(v___x_633_, 1, v___x_629_);
lean_ctor_set(v___x_633_, 2, v___x_631_);
lean_ctor_set(v___x_633_, 3, v___x_632_);
v___x_634_ = l_Lean_Syntax_node2(v_a_570_, v___y_506_, v___x_628_, v___x_633_);
v___x_635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_636_, 0, v_a_570_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_Syntax_node6(v_a_570_, v___x_586_, v___x_588_, v___x_584_, v___x_624_, v___x_627_, v___x_634_, v___x_636_);
v___x_638_ = l_Lean_Syntax_node1(v_a_570_, v___y_506_, v___x_637_);
v___x_639_ = l_Lean_Syntax_node5(v_a_570_, v___x_577_, v_fields_493_, v___x_579_, v___x_583_, v___x_584_, v___x_638_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_639_);
lean_ctor_set(v___x_495_, 0, v___x_575_);
v___x_641_ = v___x_495_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_639_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
size_t v___x_642_; size_t v___x_643_; 
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_i_486_, v___x_642_);
v_i_486_ = v___x_643_;
v_b_488_ = v___x_641_;
v___y_490_ = v_a_571_;
goto _start;
}
}
else
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___x_566_);
lean_dec(v___x_562_);
lean_dec_ref_known(v___x_554_, 2);
lean_dec(v___x_552_);
lean_dec(v___x_550_);
lean_dec(v___x_532_);
lean_dec_ref_known(v___x_528_, 2);
lean_dec(v___x_527_);
lean_dec(v___x_523_);
lean_dec(v___x_521_);
lean_dec(v___y_504_);
lean_dec(v___y_501_);
lean_dec(v___x_499_);
lean_del_object(v___x_495_);
lean_dec(v_fields_493_);
lean_dec_ref(v_cmds_492_);
lean_dec(v_vis_x3f_483_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
lean_dec(v_type_480_);
lean_dec(v_structTy_479_);
v_a_646_ = lean_ctor_get(v___x_569_, 0);
v_a_647_ = lean_ctor_get(v___x_569_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_569_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_569_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
v___jp_655_:
{
lean_object* v_methods_657_; lean_object* v_quotContext_658_; lean_object* v_currMacroScope_659_; lean_object* v_currRecDepth_660_; lean_object* v_maxRecDepth_661_; lean_object* v_ref_662_; lean_object* v___x_663_; 
v_methods_657_ = lean_ctor_get(v___y_489_, 0);
v_quotContext_658_ = lean_ctor_get(v___y_489_, 1);
v_currMacroScope_659_ = lean_ctor_get(v___y_489_, 2);
v_currRecDepth_660_ = lean_ctor_get(v___y_489_, 3);
v_maxRecDepth_661_ = lean_ctor_get(v___y_489_, 4);
v_ref_662_ = lean_ctor_get(v___y_489_, 5);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_491_, v_ref_662_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc_n(v_a_664_, 2);
v_a_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_663_, 2);
v___x_666_ = l_Lean_mkIdentFrom(v___x_497_, v___y_656_, v___x_491_);
v___x_667_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_668_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_669_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_672_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_673_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_674_, 0, v_a_664_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_673_);
if (lean_obj_tag(v_vis_x3f_483_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_676_; 
v_val_675_ = lean_ctor_get(v_vis_x3f_483_, 0);
lean_inc(v_val_675_);
v___x_676_ = l_Array_mkArray1___redArg(v_val_675_);
v___y_501_ = v___x_674_;
v___y_502_ = v_currRecDepth_660_;
v___y_503_ = v_ref_662_;
v___y_504_ = v_a_664_;
v___y_505_ = v_quotContext_658_;
v___y_506_ = v___x_672_;
v___y_507_ = v___x_670_;
v___y_508_ = v_a_665_;
v___y_509_ = v___x_668_;
v___y_510_ = v_maxRecDepth_661_;
v___y_511_ = v___x_673_;
v___y_512_ = v_currMacroScope_659_;
v___y_513_ = v___x_666_;
v___y_514_ = v_methods_657_;
v___y_515_ = v___x_669_;
v___y_516_ = v___x_667_;
v___y_517_ = v___x_671_;
v___y_518_ = v___x_676_;
goto v___jp_500_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_501_ = v___x_674_;
v___y_502_ = v_currRecDepth_660_;
v___y_503_ = v_ref_662_;
v___y_504_ = v_a_664_;
v___y_505_ = v_quotContext_658_;
v___y_506_ = v___x_672_;
v___y_507_ = v___x_670_;
v___y_508_ = v_a_665_;
v___y_509_ = v___x_668_;
v___y_510_ = v_maxRecDepth_661_;
v___y_511_ = v___x_673_;
v___y_512_ = v_currMacroScope_659_;
v___y_513_ = v___x_666_;
v___y_514_ = v_methods_657_;
v___y_515_ = v___x_669_;
v___y_516_ = v___x_667_;
v___y_517_ = v___x_671_;
v___y_518_ = v___x_677_;
goto v___jp_500_;
}
}
else
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___y_656_);
lean_dec(v___x_499_);
lean_del_object(v___x_495_);
lean_dec(v_fields_493_);
lean_dec_ref(v_cmds_492_);
lean_dec(v_vis_x3f_483_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
lean_dec(v_type_480_);
lean_dec(v_structTy_479_);
v_a_678_ = lean_ctor_get(v___x_663_, 0);
v_a_679_ = lean_ctor_get(v___x_663_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_663_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_inc(v_a_678_);
lean_dec(v___x_663_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_vis_x3f_483_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
lean_dec(v_type_480_);
lean_dec(v_structTy_479_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_b_488_);
lean_ctor_set(v___x_704_, 1, v___y_490_);
return v___x_704_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_structTy_479_ = stack[0].m_obj;
lean_object* v_type_480_ = stack[1].m_obj;
lean_object* v___x_481_ = stack[2].m_obj;
lean_object* v___x_482_ = stack[3].m_obj;
lean_object* v_vis_x3f_483_ = stack[4].m_obj;
lean_object* v_structId_484_ = stack[5].m_obj;
lean_object* v_as_485_ = stack[6].m_obj;
size_t v_i_486_ = stack[7].m_num;
size_t v_stop_487_ = stack[8].m_num;
lean_object* v_b_488_ = stack[9].m_obj;
lean_object* v___y_489_ = stack[10].m_obj;
lean_object* v___y_490_ = stack[11].m_obj;
lean_object* v_res_705_;
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(v_structTy_479_, v_type_480_, v___x_481_, v___x_482_, v_vis_x3f_483_, v_structId_484_, v_as_485_, v_i_486_, v_stop_487_, v_b_488_, v___y_489_, v___y_490_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___boxed(lean_object* v_structTy_706_, lean_object* v_type_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v_vis_x3f_710_, lean_object* v_structId_711_, lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(v_structTy_706_, v_type_707_, v___x_708_, v___x_709_, v_vis_x3f_710_, v_structId_711_, v_as_712_, v_i_boxed_718_, v_stop_boxed_719_, v_b_715_, v___y_716_, v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_712_);
lean_dec(v_structId_711_);
return v_res_720_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(lean_object* v_structTy_721_, lean_object* v_type_722_, lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v_vis_x3f_725_, lean_object* v_structId_726_, lean_object* v_as_727_, size_t v_i_728_, size_t v_stop_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
if (v___x_733_ == 0)
{
lean_object* v_cmds_734_; lean_object* v_fields_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_945_; 
v_cmds_734_ = lean_ctor_get(v_b_730_, 0);
v_fields_735_ = lean_ctor_get(v_b_730_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_b_730_);
if (v_isSharedCheck_945_ == 0)
{
v___x_737_ = v_b_730_;
v_isShared_738_ = v_isSharedCheck_945_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_fields_735_);
lean_inc(v_cmds_734_);
lean_dec(v_b_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_945_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_898_; uint8_t v___x_929_; 
v___x_739_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
v___x_740_ = l_Lean_TSyntax_getId(v___x_739_);
lean_inc(v___x_740_);
lean_inc(v___x_739_);
v___x_741_ = l_Lake_Name_quoteFrom(v___x_739_, v___x_740_, v___x_733_);
v___x_929_ = l_Lean_Name_hasMacroScopes(v___x_740_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_726_, v___x_740_);
v___y_898_ = v___x_930_;
goto v___jp_897_;
}
else
{
lean_object* v_view_931_; lean_object* v_name_932_; lean_object* v_imported_933_; lean_object* v_ctx_934_; lean_object* v_scopes_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_944_; 
v_view_931_ = l_Lean_extractMacroScopes(v___x_740_);
v_name_932_ = lean_ctor_get(v_view_931_, 0);
v_imported_933_ = lean_ctor_get(v_view_931_, 1);
v_ctx_934_ = lean_ctor_get(v_view_931_, 2);
v_scopes_935_ = lean_ctor_get(v_view_931_, 3);
v_isSharedCheck_944_ = !lean_is_exclusive(v_view_931_);
if (v_isSharedCheck_944_ == 0)
{
v___x_937_ = v_view_931_;
v_isShared_938_ = v_isSharedCheck_944_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_scopes_935_);
lean_inc(v_ctx_934_);
lean_inc(v_imported_933_);
lean_inc(v_name_932_);
lean_dec(v_view_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_944_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_726_, v_name_932_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_imported_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_ctx_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_scopes_935_);
v___x_941_ = v_reuseFailAlloc_943_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_MacroScopesView_review(v___x_941_);
v___y_898_ = v___x_942_;
goto v___jp_897_;
}
}
}
v___jp_742_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_ref_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_inc_ref(v___y_751_);
v___x_761_ = l_Array_append___redArg(v___y_751_, v___y_760_);
lean_dec_ref(v___y_760_);
lean_inc_n(v___y_748_, 4);
lean_inc_n(v___y_757_, 18);
v___x_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_762_, 0, v___y_757_);
lean_ctor_set(v___x_762_, 1, v___y_748_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
lean_inc_n(v___y_744_, 11);
lean_inc(v___y_752_);
v___x_763_ = l_Lean_Syntax_node7(v___y_757_, v___y_752_, v___y_744_, v___y_744_, v___x_762_, v___y_744_, v___y_744_, v___y_744_, v___y_744_);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_758_, 4);
lean_inc_ref_n(v___y_745_, 9);
lean_inc_ref_n(v___y_747_, 9);
v___x_765_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___y_758_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
v___x_768_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node1(v___y_757_, v___x_768_, v___y_744_);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_757_);
lean_ctor_set(v___x_770_, 1, v___x_764_);
v___x_771_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_772_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___y_758_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___y_757_, v___x_772_, v___y_749_, v___y_744_);
v___x_774_ = l_Lean_Syntax_node1(v___y_757_, v___y_748_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_776_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___y_758_, v___x_775_);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_778_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_777_);
v___x_779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___y_757_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_782_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_750_, 2);
lean_inc_n(v___y_759_, 2);
v___x_785_ = l_Lean_addMacroScope(v___y_759_, v___x_784_, v___y_750_);
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__12));
v___x_788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_788_, 0, v___y_757_);
lean_ctor_set(v___x_788_, 1, v___x_783_);
lean_ctor_set(v___x_788_, 2, v___x_785_);
lean_ctor_set(v___x_788_, 3, v___x_787_);
lean_inc(v_type_722_);
lean_inc(v___x_741_);
lean_inc(v_structTy_721_);
v___x_789_ = l_Lean_Syntax_node3(v___y_757_, v___y_748_, v_structTy_721_, v___x_741_, v_type_722_);
v___x_790_ = l_Lean_Syntax_node2(v___y_757_, v___x_782_, v___x_788_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node2(v___y_757_, v___x_778_, v___x_780_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node2(v___y_757_, v___x_776_, v___y_744_, v___x_791_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_794_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___y_758_, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_757_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_798_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_797_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___y_757_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_inc(v___x_723_);
v___x_801_ = l_Lean_Syntax_node1(v___y_757_, v___y_748_, v___x_723_);
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_757_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_Syntax_node3(v___y_757_, v___x_798_, v___x_800_, v___x_801_, v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_807_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_805_, v___x_806_);
v___x_808_ = l_Lean_Syntax_node2(v___y_757_, v___x_807_, v___y_744_, v___y_744_);
v_ref_809_ = l_Lean_replaceRef(v_fields_735_, v___y_755_);
lean_inc(v_ref_809_);
lean_inc(v___y_754_);
lean_inc(v___y_743_);
lean_inc(v___y_756_);
v___x_810_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_810_, 0, v___y_756_);
lean_ctor_set(v___x_810_, 1, v___y_759_);
lean_ctor_set(v___x_810_, 2, v___y_750_);
lean_ctor_set(v___x_810_, 3, v___y_743_);
lean_ctor_set(v___x_810_, 4, v___y_754_);
lean_ctor_set(v___x_810_, 5, v_ref_809_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_733_, v_ref_809_, v___x_810_, v___y_746_);
lean_dec_ref_known(v___x_810_, 6);
lean_dec(v_ref_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_n(v_a_812_, 30);
v_a_813_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_811_, 2);
lean_inc(v___y_744_);
lean_inc_n(v___y_757_, 2);
v___x_814_ = l_Lean_Syntax_node4(v___y_757_, v___x_794_, v___x_796_, v___x_804_, v___x_808_, v___y_744_);
v___x_815_ = l_Lean_Syntax_node6(v___y_757_, v___x_765_, v___x_769_, v___x_770_, v___y_744_, v___x_774_, v___x_792_, v___x_814_);
lean_inc(v___y_753_);
v___x_816_ = l_Lean_Syntax_node2(v___y_757_, v___y_753_, v___x_763_, v___x_815_);
v___x_817_ = lean_array_push(v_cmds_734_, v___x_816_);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_745_, 7);
lean_inc_ref_n(v___y_747_, 7);
v___x_819_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_818_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_812_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_750_, 5);
lean_inc_n(v___y_759_, 5);
v___x_824_ = l_Lean_addMacroScope(v___y_759_, v___x_823_, v___y_750_);
v___x_825_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_825_, 0, v_a_812_);
lean_ctor_set(v___x_825_, 1, v___x_822_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
lean_ctor_set(v___x_825_, 3, v___x_786_);
lean_inc_ref(v___y_751_);
lean_inc_n(v___y_748_, 7);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v_a_812_);
lean_ctor_set(v___x_826_, 1, v___y_748_);
lean_ctor_set(v___x_826_, 2, v___y_751_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_828_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_827_);
v___x_829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v_a_812_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_832_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_831_);
v___x_833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_834_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_836_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_835_);
v___x_837_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_839_ = l_Lean_addMacroScope(v___y_759_, v___x_838_, v___y_750_);
v___x_840_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_840_, 0, v_a_812_);
lean_ctor_set(v___x_840_, 1, v___x_837_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
lean_ctor_set(v___x_840_, 3, v___x_786_);
lean_inc_ref_n(v___x_826_, 17);
lean_inc_n(v___x_836_, 2);
v___x_841_ = l_Lean_Syntax_node2(v_a_812_, v___x_836_, v___x_840_, v___x_826_);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_843_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_842_);
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v_a_812_);
lean_ctor_set(v___x_844_, 1, v___x_795_);
lean_inc_ref_n(v___x_844_, 2);
lean_inc_n(v___x_843_, 2);
v___x_845_ = l_Lean_Syntax_node3(v_a_812_, v___x_843_, v___x_844_, v___x_826_, v___x_741_);
v___x_846_ = l_Lean_Syntax_node3(v_a_812_, v___y_748_, v___x_826_, v___x_826_, v___x_845_);
lean_inc_n(v___x_834_, 2);
v___x_847_ = l_Lean_Syntax_node2(v_a_812_, v___x_834_, v___x_841_, v___x_846_);
v___x_848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_850_ = l_Lean_addMacroScope(v___y_759_, v___x_849_, v___y_750_);
v___x_851_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_851_, 0, v_a_812_);
lean_ctor_set(v___x_851_, 1, v___x_848_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_ctor_set(v___x_851_, 3, v___x_786_);
v___x_852_ = l_Lean_Syntax_node2(v_a_812_, v___x_836_, v___x_851_, v___x_826_);
lean_inc(v___x_724_);
v___x_853_ = l_Lean_Syntax_node3(v_a_812_, v___x_843_, v___x_844_, v___x_826_, v___x_724_);
v___x_854_ = l_Lean_Syntax_node3(v_a_812_, v___y_748_, v___x_826_, v___x_826_, v___x_853_);
v___x_855_ = l_Lean_Syntax_node2(v_a_812_, v___x_834_, v___x_852_, v___x_854_);
v___x_856_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_858_ = l_Lean_addMacroScope(v___y_759_, v___x_857_, v___y_750_);
v___x_859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_859_, 0, v_a_812_);
lean_ctor_set(v___x_859_, 1, v___x_856_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
lean_ctor_set(v___x_859_, 3, v___x_786_);
v___x_860_ = l_Lean_Syntax_node2(v_a_812_, v___x_836_, v___x_859_, v___x_826_);
v___x_861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__41);
v___x_862_ = l_Lean_Syntax_node3(v_a_812_, v___x_843_, v___x_844_, v___x_826_, v___x_861_);
v___x_863_ = l_Lean_Syntax_node3(v_a_812_, v___y_748_, v___x_826_, v___x_826_, v___x_862_);
v___x_864_ = l_Lean_Syntax_node2(v_a_812_, v___x_834_, v___x_860_, v___x_863_);
v___x_865_ = l_Lean_Syntax_node6(v_a_812_, v___y_748_, v___x_847_, v___x_826_, v___x_855_, v___x_826_, v___x_864_, v___x_826_);
v___x_866_ = l_Lean_Syntax_node1(v_a_812_, v___x_832_, v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_868_ = l_Lean_Name_mkStr4(v___y_747_, v___y_745_, v___x_766_, v___x_867_);
v___x_869_ = l_Lean_Syntax_node1(v_a_812_, v___x_868_, v___x_826_);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v_a_812_);
lean_ctor_set(v___x_870_, 1, v___x_779_);
v___x_871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_873_ = l_Lean_addMacroScope(v___y_759_, v___x_872_, v___y_750_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__50));
v___x_875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_875_, 0, v_a_812_);
lean_ctor_set(v___x_875_, 1, v___x_871_);
lean_ctor_set(v___x_875_, 2, v___x_873_);
lean_ctor_set(v___x_875_, 3, v___x_874_);
v___x_876_ = l_Lean_Syntax_node2(v_a_812_, v___y_748_, v___x_870_, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v_a_812_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_Syntax_node6(v_a_812_, v___x_828_, v___x_830_, v___x_826_, v___x_866_, v___x_869_, v___x_876_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node1(v_a_812_, v___y_748_, v___x_879_);
v___x_881_ = l_Lean_Syntax_node5(v_a_812_, v___x_819_, v_fields_735_, v___x_821_, v___x_825_, v___x_826_, v___x_880_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_881_);
lean_ctor_set(v___x_737_, 0, v___x_817_);
v___x_883_ = v___x_737_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_728_, v___x_884_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2(v_structTy_721_, v_type_722_, v___x_723_, v___x_724_, v_vis_x3f_725_, v_structId_726_, v_as_727_, v___x_885_, v_stop_729_, v___x_883_, v___y_731_, v_a_813_);
return v___x_886_;
}
}
else
{
lean_object* v_a_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v___x_808_);
lean_dec(v___x_804_);
lean_dec_ref_known(v___x_796_, 2);
lean_dec(v___x_794_);
lean_dec(v___x_792_);
lean_dec(v___x_774_);
lean_dec_ref_known(v___x_770_, 2);
lean_dec(v___x_769_);
lean_dec(v___x_765_);
lean_dec(v___x_763_);
lean_dec(v___y_757_);
lean_dec(v___y_744_);
lean_dec(v___x_741_);
lean_del_object(v___x_737_);
lean_dec(v_fields_735_);
lean_dec_ref(v_cmds_734_);
lean_dec(v_vis_x3f_725_);
lean_dec(v___x_724_);
lean_dec(v___x_723_);
lean_dec(v_type_722_);
lean_dec(v_structTy_721_);
v_a_888_ = lean_ctor_get(v___x_811_, 0);
v_a_889_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_811_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_inc(v_a_888_);
lean_dec(v___x_811_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_888_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_897_:
{
lean_object* v_methods_899_; lean_object* v_quotContext_900_; lean_object* v_currMacroScope_901_; lean_object* v_currRecDepth_902_; lean_object* v_maxRecDepth_903_; lean_object* v_ref_904_; lean_object* v___x_905_; 
v_methods_899_ = lean_ctor_get(v___y_731_, 0);
v_quotContext_900_ = lean_ctor_get(v___y_731_, 1);
v_currMacroScope_901_ = lean_ctor_get(v___y_731_, 2);
v_currRecDepth_902_ = lean_ctor_get(v___y_731_, 3);
v_maxRecDepth_903_ = lean_ctor_get(v___y_731_, 4);
v_ref_904_ = lean_ctor_get(v___y_731_, 5);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_733_, v_ref_904_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_n(v_a_906_, 2);
v_a_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_905_, 2);
v___x_908_ = l_Lean_mkIdentFrom(v___x_739_, v___y_898_, v___x_733_);
v___x_909_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_910_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_911_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_914_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_915_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_916_, 0, v_a_906_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
if (lean_obj_tag(v_vis_x3f_725_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; 
v_val_917_ = lean_ctor_get(v_vis_x3f_725_, 0);
lean_inc(v_val_917_);
v___x_918_ = l_Array_mkArray1___redArg(v_val_917_);
v___y_743_ = v_currRecDepth_902_;
v___y_744_ = v___x_916_;
v___y_745_ = v___x_910_;
v___y_746_ = v_a_907_;
v___y_747_ = v___x_909_;
v___y_748_ = v___x_914_;
v___y_749_ = v___x_908_;
v___y_750_ = v_currMacroScope_901_;
v___y_751_ = v___x_915_;
v___y_752_ = v___x_913_;
v___y_753_ = v___x_912_;
v___y_754_ = v_maxRecDepth_903_;
v___y_755_ = v_ref_904_;
v___y_756_ = v_methods_899_;
v___y_757_ = v_a_906_;
v___y_758_ = v___x_911_;
v___y_759_ = v_quotContext_900_;
v___y_760_ = v___x_918_;
goto v___jp_742_;
}
else
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_743_ = v_currRecDepth_902_;
v___y_744_ = v___x_916_;
v___y_745_ = v___x_910_;
v___y_746_ = v_a_907_;
v___y_747_ = v___x_909_;
v___y_748_ = v___x_914_;
v___y_749_ = v___x_908_;
v___y_750_ = v_currMacroScope_901_;
v___y_751_ = v___x_915_;
v___y_752_ = v___x_913_;
v___y_753_ = v___x_912_;
v___y_754_ = v_maxRecDepth_903_;
v___y_755_ = v_ref_904_;
v___y_756_ = v_methods_899_;
v___y_757_ = v_a_906_;
v___y_758_ = v___x_911_;
v___y_759_ = v_quotContext_900_;
v___y_760_ = v___x_919_;
goto v___jp_742_;
}
}
else
{
lean_object* v_a_920_; lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v___y_898_);
lean_dec(v___x_741_);
lean_del_object(v___x_737_);
lean_dec(v_fields_735_);
lean_dec_ref(v_cmds_734_);
lean_dec(v_vis_x3f_725_);
lean_dec(v___x_724_);
lean_dec(v___x_723_);
lean_dec(v_type_722_);
lean_dec(v_structTy_721_);
v_a_920_ = lean_ctor_get(v___x_905_, 0);
v_a_921_ = lean_ctor_get(v___x_905_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_905_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_inc(v_a_920_);
lean_dec(v___x_905_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_vis_x3f_725_);
lean_dec(v___x_724_);
lean_dec(v___x_723_);
lean_dec(v_type_722_);
lean_dec(v_structTy_721_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_b_730_);
lean_ctor_set(v___x_946_, 1, v___y_732_);
return v___x_946_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_structTy_721_ = stack[0].m_obj;
lean_object* v_type_722_ = stack[1].m_obj;
lean_object* v___x_723_ = stack[2].m_obj;
lean_object* v___x_724_ = stack[3].m_obj;
lean_object* v_vis_x3f_725_ = stack[4].m_obj;
lean_object* v_structId_726_ = stack[5].m_obj;
lean_object* v_as_727_ = stack[6].m_obj;
size_t v_i_728_ = stack[7].m_num;
size_t v_stop_729_ = stack[8].m_num;
lean_object* v_b_730_ = stack[9].m_obj;
lean_object* v___y_731_ = stack[10].m_obj;
lean_object* v___y_732_ = stack[11].m_obj;
lean_object* v_res_947_;
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_721_, v_type_722_, v___x_723_, v___x_724_, v_vis_x3f_725_, v_structId_726_, v_as_727_, v_i_728_, v_stop_729_, v_b_730_, v___y_731_, v___y_732_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___boxed(lean_object* v_structTy_948_, lean_object* v_type_949_, lean_object* v___x_950_, lean_object* v___x_951_, lean_object* v_vis_x3f_952_, lean_object* v_structId_953_, lean_object* v_as_954_, lean_object* v_i_955_, lean_object* v_stop_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_955_);
lean_dec(v_i_955_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_956_);
lean_dec(v_stop_956_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_948_, v_type_949_, v___x_950_, v___x_951_, v_vis_x3f_952_, v_structId_953_, v_as_954_, v_i_boxed_960_, v_stop_boxed_961_, v_b_957_, v___y_958_, v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v_as_954_);
lean_dec(v_structId_953_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(lean_object* v_structId_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = l_Lean_TSyntax_getId(v_structId_964_);
v___x_967_ = l_Lean_Name_append(v___x_966_, v_x_965_);
v___x_968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___closed__0));
v___x_969_ = l_Lean_Name_str___override(v___x_967_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0___boxed(lean_object* v_structId_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_970_, v_x_971_);
lean_dec(v_structId_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(lean_object* v_structId_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = l_Lean_TSyntax_getId(v_structId_974_);
v___x_977_ = l_Lean_Name_append(v___x_976_, v_x_975_);
v___x_978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___closed__0));
v___x_979_ = l_Lean_Name_str___override(v___x_977_, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2___boxed(lean_object* v_structId_980_, lean_object* v_x_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_980_, v_x_981_);
lean_dec(v_structId_980_);
return v_res_982_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
v___x_988_ = l_Lean_mkCIdent(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_991_ = l_String_toRawSubstring_x27(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__6));
v___x_996_ = l_String_toRawSubstring_x27(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__14));
v___x_1007_ = l_String_toRawSubstring_x27(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__17));
v___x_1011_ = l_String_toRawSubstring_x27(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__23));
v___x_1020_ = l_String_toRawSubstring_x27(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__0));
v___x_1024_ = l_String_toRawSubstring_x27(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__31));
v___x_1032_ = l_String_toRawSubstring_x27(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__41));
v___x_1053_ = l_String_toRawSubstring_x27(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__48));
v___x_1068_ = l_String_toRawSubstring_x27(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__53));
v___x_1075_ = l_String_toRawSubstring_x27(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__60));
v___x_1090_ = l_String_toRawSubstring_x27(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__64));
v___x_1096_ = l_String_toRawSubstring_x27(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__69));
v___x_1107_ = l_String_toRawSubstring_x27(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__72));
v___x_1112_ = l_String_toRawSubstring_x27(v___x_1111_);
return v___x_1112_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(lean_object* v_structTy_1118_, lean_object* v___x_1119_, lean_object* v_vis_x3f_1120_, lean_object* v_structId_1121_, lean_object* v_as_1122_, size_t v_i_1123_, size_t v_stop_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v___y_1135_; uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_eq(v_i_1123_, v_stop_1124_);
if (v___x_1138_ == 0)
{
lean_object* v_cmds_1139_; lean_object* v_fields_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1894_; 
v_cmds_1139_ = lean_ctor_get(v_b_1125_, 0);
v_fields_1140_ = lean_ctor_get(v_b_1125_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_b_1125_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1142_ = v_b_1125_;
v_isShared_1143_ = v_isSharedCheck_1894_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_fields_1140_);
lean_inc(v_cmds_1139_);
lean_dec(v_b_1125_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1894_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v_id_1145_; lean_object* v_ids_1146_; lean_object* v_type_1147_; lean_object* v_defVal_1148_; uint8_t v_parent_1149_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___x_1652_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1858_; uint8_t v___x_1878_; 
v___x_1144_ = lean_array_uget_borrowed(v_as_1122_, v_i_1123_);
v_id_1145_ = lean_ctor_get(v___x_1144_, 2);
v_ids_1146_ = lean_ctor_get(v___x_1144_, 3);
v_type_1147_ = lean_ctor_get(v___x_1144_, 4);
v_defVal_1148_ = lean_ctor_get(v___x_1144_, 5);
v_parent_1149_ = lean_ctor_get_uint8(v___x_1144_, sizeof(void*)*7);
v___x_1652_ = l_Lean_TSyntax_getId(v_id_1145_);
v___x_1878_ = l_Lean_Name_hasMacroScopes(v___x_1652_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_inc(v___x_1652_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1121_, v___x_1652_);
v___y_1858_ = v___x_1879_;
goto v___jp_1857_;
}
else
{
lean_object* v_view_1880_; lean_object* v_name_1881_; lean_object* v_imported_1882_; lean_object* v_ctx_1883_; lean_object* v_scopes_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1893_; 
lean_inc(v___x_1652_);
v_view_1880_ = l_Lean_extractMacroScopes(v___x_1652_);
v_name_1881_ = lean_ctor_get(v_view_1880_, 0);
v_imported_1882_ = lean_ctor_get(v_view_1880_, 1);
v_ctx_1883_ = lean_ctor_get(v_view_1880_, 2);
v_scopes_1884_ = lean_ctor_get(v_view_1880_, 3);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_view_1880_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1886_ = v_view_1880_;
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_scopes_1884_);
lean_inc(v_ctx_1883_);
lean_inc(v_imported_1882_);
lean_inc(v_name_1881_);
lean_dec(v_view_1880_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1121_, v_name_1881_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_imported_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_ctx_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_scopes_1884_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_MacroScopesView_review(v___x_1890_);
v___y_1858_ = v___x_1891_;
goto v___jp_1857_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_inc_ref(v___y_1187_);
v___x_1191_ = l_Array_append___redArg(v___y_1187_, v___y_1190_);
lean_dec_ref(v___y_1190_);
lean_inc_n(v___y_1182_, 4);
lean_inc_n(v___y_1153_, 18);
v___x_1192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1153_);
lean_ctor_set(v___x_1192_, 1, v___y_1182_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
lean_inc_n(v___y_1151_, 11);
lean_inc(v___y_1155_);
v___x_1193_ = l_Lean_Syntax_node7(v___y_1153_, v___y_1155_, v___y_1151_, v___y_1151_, v___x_1192_, v___y_1151_, v___y_1151_, v___y_1151_, v___y_1151_);
v___x_1194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1188_, 3);
lean_inc_ref_n(v___y_1169_, 6);
lean_inc_ref_n(v___y_1160_, 6);
v___x_1195_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1188_, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1168_, 2);
v___x_1197_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1168_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_node1(v___y_1153_, v___x_1197_, v___y_1151_);
v___x_1199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___y_1153_);
lean_ctor_set(v___x_1199_, 1, v___x_1194_);
v___x_1200_ = l_Lean_Syntax_node2(v___y_1153_, v___y_1178_, v___y_1172_, v___y_1151_);
v___x_1201_ = l_Lean_Syntax_node1(v___y_1153_, v___y_1182_, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1203_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1188_, v___x_1202_);
lean_inc_ref(v___y_1159_);
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1153_);
lean_ctor_set(v___x_1204_, 1, v___y_1159_);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1157_, 2);
lean_inc_n(v___y_1174_, 2);
v___x_1208_ = l_Lean_addMacroScope(v___y_1174_, v___x_1207_, v___y_1157_);
lean_inc_ref(v___y_1158_);
v___x_1209_ = l_Lean_Name_mkStr2(v___y_1158_, v___x_1205_);
lean_inc(v___y_1154_);
lean_inc(v___x_1209_);
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___y_1154_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_inc(v___y_1183_);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___y_1183_);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1210_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1153_);
lean_ctor_set(v___x_1214_, 1, v___x_1206_);
lean_ctor_set(v___x_1214_, 2, v___x_1208_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
lean_inc(v_type_1147_);
lean_inc(v___y_1163_);
lean_inc(v_structTy_1118_);
v___x_1215_ = l_Lean_Syntax_node3(v___y_1153_, v___y_1182_, v_structTy_1118_, v___y_1163_, v_type_1147_);
v___x_1216_ = l_Lean_Syntax_node2(v___y_1153_, v___y_1175_, v___x_1214_, v___x_1215_);
v___x_1217_ = l_Lean_Syntax_node2(v___y_1153_, v___y_1176_, v___x_1204_, v___x_1216_);
v___x_1218_ = l_Lean_Syntax_node2(v___y_1153_, v___x_1203_, v___y_1151_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1220_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1188_, v___x_1219_);
lean_inc_ref(v___y_1161_);
v___x_1221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1153_);
lean_ctor_set(v___x_1221_, 1, v___y_1161_);
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1223_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1168_, v___x_1222_);
v___x_1224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___y_1153_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
lean_inc(v___y_1171_);
v___x_1226_ = l_Lean_Syntax_node1(v___y_1153_, v___y_1182_, v___y_1171_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1153_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node3(v___y_1153_, v___x_1223_, v___x_1225_, v___x_1226_, v___x_1228_);
v___x_1230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1232_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___x_1230_, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_node2(v___y_1153_, v___x_1232_, v___y_1151_, v___y_1151_);
v_ref_1234_ = l_Lean_replaceRef(v_fields_1140_, v___y_1164_);
lean_inc(v_ref_1234_);
lean_inc(v___y_1179_);
lean_inc(v___y_1162_);
lean_inc(v___y_1180_);
v___x_1235_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1235_, 0, v___y_1180_);
lean_ctor_set(v___x_1235_, 1, v___y_1174_);
lean_ctor_set(v___x_1235_, 2, v___y_1157_);
lean_ctor_set(v___x_1235_, 3, v___y_1162_);
lean_ctor_set(v___x_1235_, 4, v___y_1179_);
lean_ctor_set(v___x_1235_, 5, v_ref_1234_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1138_, v_ref_1234_, v___x_1235_, v___y_1185_);
lean_dec_ref_known(v___x_1235_, 6);
lean_dec(v_ref_1234_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_n(v_a_1237_, 30);
v_a_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1236_, 2);
lean_inc(v___y_1151_);
lean_inc_n(v___y_1153_, 2);
v___x_1239_ = l_Lean_Syntax_node4(v___y_1153_, v___x_1220_, v___x_1221_, v___x_1229_, v___x_1233_, v___y_1151_);
v___x_1240_ = l_Lean_Syntax_node6(v___y_1153_, v___x_1195_, v___x_1198_, v___x_1199_, v___y_1151_, v___x_1201_, v___x_1218_, v___x_1239_);
lean_inc(v___y_1166_);
v___x_1241_ = l_Lean_Syntax_node2(v___y_1153_, v___y_1166_, v___x_1193_, v___x_1240_);
v___x_1242_ = lean_array_push(v___y_1170_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1169_);
lean_inc_ref(v___y_1160_);
v___x_1244_ = l_Lean_Name_mkStr4(v___y_1160_, v___y_1169_, v___y_1168_, v___x_1243_);
v___x_1245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1237_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1157_, 5);
lean_inc_n(v___y_1174_, 5);
v___x_1249_ = l_Lean_addMacroScope(v___y_1174_, v___x_1248_, v___y_1157_);
lean_inc_n(v___y_1183_, 5);
v___x_1250_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1237_);
lean_ctor_set(v___x_1250_, 1, v___x_1247_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
lean_ctor_set(v___x_1250_, 3, v___y_1183_);
lean_inc_ref(v___y_1187_);
lean_inc_n(v___y_1182_, 7);
v___x_1251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1237_);
lean_ctor_set(v___x_1251_, 1, v___y_1182_);
lean_ctor_set(v___x_1251_, 2, v___y_1187_);
lean_inc_ref(v___y_1156_);
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1237_);
lean_ctor_set(v___x_1252_, 1, v___y_1156_);
v___x_1253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1255_ = l_Lean_addMacroScope(v___y_1174_, v___x_1254_, v___y_1157_);
v___x_1256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1256_, 0, v_a_1237_);
lean_ctor_set(v___x_1256_, 1, v___x_1253_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_ctor_set(v___x_1256_, 3, v___y_1183_);
lean_inc_ref_n(v___x_1251_, 17);
lean_inc_n(v___y_1189_, 2);
v___x_1257_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1189_, v___x_1256_, v___x_1251_);
lean_inc_ref(v___y_1161_);
v___x_1258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1237_);
lean_ctor_set(v___x_1258_, 1, v___y_1161_);
lean_inc_ref_n(v___x_1258_, 2);
lean_inc_n(v___y_1184_, 2);
v___x_1259_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1184_, v___x_1258_, v___x_1251_, v___y_1163_);
v___x_1260_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1182_, v___x_1251_, v___x_1251_, v___x_1259_);
lean_inc_n(v___y_1152_, 2);
v___x_1261_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1152_, v___x_1257_, v___x_1260_);
v___x_1262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1264_ = l_Lean_addMacroScope(v___y_1174_, v___x_1263_, v___y_1157_);
v___x_1265_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1237_);
lean_ctor_set(v___x_1265_, 1, v___x_1262_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
lean_ctor_set(v___x_1265_, 3, v___y_1183_);
v___x_1266_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1189_, v___x_1265_, v___x_1251_);
lean_inc(v___y_1165_);
v___x_1267_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1184_, v___x_1258_, v___x_1251_, v___y_1165_);
v___x_1268_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1182_, v___x_1251_, v___x_1251_, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1152_, v___x_1266_, v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_1271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_1272_ = l_Lean_addMacroScope(v___y_1174_, v___x_1271_, v___y_1157_);
v___x_1273_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1273_, 0, v_a_1237_);
lean_ctor_set(v___x_1273_, 1, v___x_1270_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
lean_ctor_set(v___x_1273_, 3, v___y_1183_);
v___x_1274_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1189_, v___x_1273_, v___x_1251_);
v___x_1275_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_1276_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1184_, v___x_1258_, v___x_1251_, v___x_1275_);
v___x_1277_ = l_Lean_Syntax_node3(v_a_1237_, v___y_1182_, v___x_1251_, v___x_1251_, v___x_1276_);
v___x_1278_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1152_, v___x_1274_, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node6(v_a_1237_, v___y_1182_, v___x_1261_, v___x_1251_, v___x_1269_, v___x_1251_, v___x_1278_, v___x_1251_);
v___x_1280_ = l_Lean_Syntax_node1(v_a_1237_, v___y_1177_, v___x_1279_);
v___x_1281_ = l_Lean_Syntax_node1(v_a_1237_, v___y_1181_, v___x_1251_);
lean_inc_ref(v___y_1159_);
v___x_1282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1237_);
lean_ctor_set(v___x_1282_, 1, v___y_1159_);
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1284_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1286_ = l_Lean_addMacroScope(v___y_1174_, v___x_1285_, v___y_1157_);
lean_inc_ref(v___y_1158_);
v___x_1287_ = l_Lean_Name_mkStr2(v___y_1158_, v___x_1283_);
lean_inc(v___y_1154_);
lean_inc(v___x_1287_);
v___x_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___y_1154_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
v___x_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___y_1183_);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1288_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1237_);
lean_ctor_set(v___x_1292_, 1, v___x_1284_);
lean_ctor_set(v___x_1292_, 2, v___x_1286_);
lean_ctor_set(v___x_1292_, 3, v___x_1291_);
v___x_1293_ = l_Lean_Syntax_node2(v_a_1237_, v___y_1182_, v___x_1282_, v___x_1292_);
lean_inc_ref(v___y_1167_);
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1237_);
lean_ctor_set(v___x_1294_, 1, v___y_1167_);
v___x_1295_ = l_Lean_Syntax_node6(v_a_1237_, v___y_1173_, v___x_1252_, v___x_1251_, v___x_1280_, v___x_1281_, v___x_1293_, v___x_1294_);
v___x_1296_ = l_Lean_Syntax_node1(v_a_1237_, v___y_1182_, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node5(v_a_1237_, v___x_1244_, v_fields_1140_, v___x_1246_, v___x_1250_, v___x_1251_, v___x_1296_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1297_);
lean_ctor_set(v___x_1142_, 0, v___x_1242_);
v___x_1299_ = v___x_1142_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_dec_lt(v___x_1300_, v___y_1186_);
if (v___x_1301_ == 0)
{
lean_dec(v___y_1186_);
lean_dec(v___y_1171_);
lean_dec(v___y_1165_);
v_a_1129_ = v___x_1299_;
v_a_1130_ = v_a_1238_;
goto v___jp_1128_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_le(v___y_1186_, v___y_1186_);
if (v___x_1302_ == 0)
{
if (v___x_1301_ == 0)
{
lean_dec(v___y_1186_);
lean_dec(v___y_1171_);
lean_dec(v___y_1165_);
v_a_1129_ = v___x_1299_;
v_a_1130_ = v_a_1238_;
goto v___jp_1128_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_of_nat(v___y_1186_);
lean_dec(v___y_1186_);
lean_inc(v_vis_x3f_1120_);
lean_inc(v_type_1147_);
lean_inc(v_structTy_1118_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1118_, v_type_1147_, v___y_1171_, v___y_1165_, v_vis_x3f_1120_, v_structId_1121_, v_ids_1146_, v___x_1303_, v___x_1304_, v___x_1299_, v___y_1126_, v_a_1238_);
v___y_1135_ = v___x_1305_;
goto v___jp_1134_;
}
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_of_nat(v___y_1186_);
lean_dec(v___y_1186_);
lean_inc(v_vis_x3f_1120_);
lean_inc(v_type_1147_);
lean_inc(v_structTy_1118_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1118_, v_type_1147_, v___y_1171_, v___y_1165_, v_vis_x3f_1120_, v_structId_1121_, v_ids_1146_, v___x_1306_, v___x_1307_, v___x_1299_, v___y_1126_, v_a_1238_);
v___y_1135_ = v___x_1308_;
goto v___jp_1134_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v___x_1233_);
lean_dec(v___x_1229_);
lean_dec_ref_known(v___x_1221_, 2);
lean_dec(v___x_1220_);
lean_dec(v___x_1218_);
lean_dec(v___x_1201_);
lean_dec_ref_known(v___x_1199_, 2);
lean_dec(v___x_1198_);
lean_dec(v___x_1195_);
lean_dec(v___x_1193_);
lean_dec(v___y_1189_);
lean_dec(v___y_1186_);
lean_dec(v___y_1184_);
lean_dec(v___y_1181_);
lean_dec(v___y_1177_);
lean_dec(v___y_1173_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1165_);
lean_dec(v___y_1163_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec(v___y_1151_);
lean_del_object(v___x_1142_);
lean_dec(v_fields_1140_);
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v_a_1310_ = lean_ctor_get(v___x_1236_, 0);
v_a_1311_ = lean_ctor_get(v___x_1236_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1236_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_inc(v_a_1310_);
lean_dec(v___x_1236_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1310_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
v___jp_1319_:
{
lean_object* v___x_1358_; 
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1138_, v___y_1331_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_n(v_a_1359_, 2);
v_a_1360_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1358_, 2);
v___x_1361_ = l_Lean_mkIdentFrom(v___y_1354_, v___y_1357_, v___x_1138_);
lean_dec(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v___y_1350_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1359_);
lean_ctor_set(v___x_1362_, 1, v___y_1350_);
lean_ctor_set(v___x_1362_, 2, v___y_1353_);
if (lean_obj_tag(v_vis_x3f_1120_) == 1)
{
lean_object* v_val_1363_; lean_object* v___x_1364_; 
v_val_1363_ = lean_ctor_get(v_vis_x3f_1120_, 0);
lean_inc(v_val_1363_);
v___x_1364_ = l_Array_mkArray1___redArg(v_val_1363_);
v___y_1151_ = v___x_1362_;
v___y_1152_ = v___y_1320_;
v___y_1153_ = v_a_1359_;
v___y_1154_ = v___y_1321_;
v___y_1155_ = v___y_1322_;
v___y_1156_ = v___y_1326_;
v___y_1157_ = v___y_1325_;
v___y_1158_ = v___y_1324_;
v___y_1159_ = v___y_1328_;
v___y_1160_ = v___y_1327_;
v___y_1161_ = v___y_1329_;
v___y_1162_ = v___y_1330_;
v___y_1163_ = v___y_1332_;
v___y_1164_ = v___y_1331_;
v___y_1165_ = v___y_1333_;
v___y_1166_ = v___y_1334_;
v___y_1167_ = v___y_1335_;
v___y_1168_ = v___y_1336_;
v___y_1169_ = v___y_1337_;
v___y_1170_ = v___y_1338_;
v___y_1171_ = v___y_1339_;
v___y_1172_ = v___x_1361_;
v___y_1173_ = v___y_1340_;
v___y_1174_ = v___y_1342_;
v___y_1175_ = v___y_1343_;
v___y_1176_ = v___y_1341_;
v___y_1177_ = v___y_1345_;
v___y_1178_ = v___y_1344_;
v___y_1179_ = v___y_1347_;
v___y_1180_ = v___y_1346_;
v___y_1181_ = v___y_1349_;
v___y_1182_ = v___y_1350_;
v___y_1183_ = v___y_1348_;
v___y_1184_ = v___y_1351_;
v___y_1185_ = v_a_1360_;
v___y_1186_ = v___y_1352_;
v___y_1187_ = v___y_1353_;
v___y_1188_ = v___y_1355_;
v___y_1189_ = v___y_1356_;
v___y_1190_ = v___x_1364_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_mk_empty_array_with_capacity(v___y_1323_);
v___y_1151_ = v___x_1362_;
v___y_1152_ = v___y_1320_;
v___y_1153_ = v_a_1359_;
v___y_1154_ = v___y_1321_;
v___y_1155_ = v___y_1322_;
v___y_1156_ = v___y_1326_;
v___y_1157_ = v___y_1325_;
v___y_1158_ = v___y_1324_;
v___y_1159_ = v___y_1328_;
v___y_1160_ = v___y_1327_;
v___y_1161_ = v___y_1329_;
v___y_1162_ = v___y_1330_;
v___y_1163_ = v___y_1332_;
v___y_1164_ = v___y_1331_;
v___y_1165_ = v___y_1333_;
v___y_1166_ = v___y_1334_;
v___y_1167_ = v___y_1335_;
v___y_1168_ = v___y_1336_;
v___y_1169_ = v___y_1337_;
v___y_1170_ = v___y_1338_;
v___y_1171_ = v___y_1339_;
v___y_1172_ = v___x_1361_;
v___y_1173_ = v___y_1340_;
v___y_1174_ = v___y_1342_;
v___y_1175_ = v___y_1343_;
v___y_1176_ = v___y_1341_;
v___y_1177_ = v___y_1345_;
v___y_1178_ = v___y_1344_;
v___y_1179_ = v___y_1347_;
v___y_1180_ = v___y_1346_;
v___y_1181_ = v___y_1349_;
v___y_1182_ = v___y_1350_;
v___y_1183_ = v___y_1348_;
v___y_1184_ = v___y_1351_;
v___y_1185_ = v_a_1360_;
v___y_1186_ = v___y_1352_;
v___y_1187_ = v___y_1353_;
v___y_1188_ = v___y_1355_;
v___y_1189_ = v___y_1356_;
v___y_1190_ = v___x_1365_;
goto v___jp_1150_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v___y_1354_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1349_);
lean_dec(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1320_);
lean_del_object(v___x_1142_);
lean_dec(v_fields_1140_);
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v_a_1366_ = lean_ctor_get(v___x_1358_, 0);
v_a_1367_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_inc(v_a_1366_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1366_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
v___jp_1375_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_ref_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_inc_ref(v___y_1410_);
v___x_1414_ = l_Array_append___redArg(v___y_1410_, v___y_1413_);
lean_dec_ref(v___y_1413_);
lean_inc_n(v___y_1405_, 4);
lean_inc_n(v___y_1409_, 18);
v___x_1415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1415_, 0, v___y_1409_);
lean_ctor_set(v___x_1415_, 1, v___y_1405_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
lean_inc_n(v___y_1389_, 11);
lean_inc(v___y_1378_);
v___x_1416_ = l_Lean_Syntax_node7(v___y_1409_, v___y_1378_, v___y_1389_, v___y_1389_, v___x_1415_, v___y_1389_, v___y_1389_, v___y_1389_, v___y_1389_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1411_, 3);
lean_inc_ref_n(v___y_1393_, 6);
lean_inc_ref_n(v___y_1383_, 6);
v___x_1418_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1411_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1392_, 2);
v___x_1420_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1392_, v___x_1419_);
v___x_1421_ = l_Lean_Syntax_node1(v___y_1409_, v___x_1420_, v___y_1389_);
v___x_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1409_);
lean_ctor_set(v___x_1422_, 1, v___x_1417_);
v___x_1423_ = l_Lean_Syntax_node2(v___y_1409_, v___y_1401_, v___y_1408_, v___y_1389_);
v___x_1424_ = l_Lean_Syntax_node1(v___y_1409_, v___y_1405_, v___x_1423_);
v___x_1425_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1426_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1411_, v___x_1425_);
lean_inc_ref(v___y_1382_);
v___x_1427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1409_);
lean_ctor_set(v___x_1427_, 1, v___y_1382_);
v___x_1428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_1429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_1430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_1380_, 2);
lean_inc_n(v___y_1397_, 2);
v___x_1431_ = l_Lean_addMacroScope(v___y_1397_, v___x_1430_, v___y_1380_);
lean_inc_ref(v___y_1381_);
v___x_1432_ = l_Lean_Name_mkStr2(v___y_1381_, v___x_1428_);
lean_inc(v___y_1377_);
lean_inc(v___x_1432_);
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___y_1377_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_inc(v___y_1406_);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___y_1406_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1433_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1409_);
lean_ctor_set(v___x_1437_, 1, v___x_1429_);
lean_ctor_set(v___x_1437_, 2, v___x_1431_);
lean_ctor_set(v___x_1437_, 3, v___x_1436_);
lean_inc(v_type_1147_);
lean_inc(v_structTy_1118_);
v___x_1438_ = l_Lean_Syntax_node2(v___y_1409_, v___y_1405_, v_structTy_1118_, v_type_1147_);
lean_inc(v___y_1398_);
v___x_1439_ = l_Lean_Syntax_node2(v___y_1409_, v___y_1398_, v___x_1437_, v___x_1438_);
v___x_1440_ = l_Lean_Syntax_node2(v___y_1409_, v___y_1399_, v___x_1427_, v___x_1439_);
v___x_1441_ = l_Lean_Syntax_node2(v___y_1409_, v___x_1426_, v___y_1389_, v___x_1440_);
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_1443_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1411_, v___x_1442_);
lean_inc_ref(v___y_1384_);
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1409_);
lean_ctor_set(v___x_1444_, 1, v___y_1384_);
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_1446_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1392_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1409_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l_Lean_Syntax_node1(v___y_1409_, v___y_1405_, v___y_1395_);
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_1451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1409_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_node3(v___y_1409_, v___x_1446_, v___x_1448_, v___x_1449_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_1455_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___x_1453_, v___x_1454_);
v___x_1456_ = l_Lean_Syntax_node2(v___y_1409_, v___x_1455_, v___y_1389_, v___y_1389_);
v_ref_1457_ = l_Lean_replaceRef(v_fields_1140_, v___y_1386_);
lean_inc(v_ref_1457_);
lean_inc(v___y_1403_);
lean_inc(v___y_1385_);
lean_inc(v___y_1402_);
v___x_1458_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1458_, 0, v___y_1402_);
lean_ctor_set(v___x_1458_, 1, v___y_1397_);
lean_ctor_set(v___x_1458_, 2, v___y_1380_);
lean_ctor_set(v___x_1458_, 3, v___y_1385_);
lean_ctor_set(v___x_1458_, 4, v___y_1403_);
lean_ctor_set(v___x_1458_, 5, v_ref_1457_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1138_, v_ref_1457_, v___x_1458_, v___y_1390_);
lean_dec_ref_known(v___x_1458_, 6);
lean_dec(v_ref_1457_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_ref_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_n(v_a_1460_, 14);
v_a_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1459_, 2);
v___x_1462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_1392_, 2);
lean_inc_ref_n(v___y_1393_, 5);
lean_inc_ref_n(v___y_1383_, 7);
v___x_1463_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1392_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_1465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1460_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_1467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_1380_, 4);
lean_inc_n(v___y_1397_, 4);
v___x_1468_ = l_Lean_addMacroScope(v___y_1397_, v___x_1467_, v___y_1380_);
lean_inc_n(v___y_1406_, 3);
v___x_1469_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1460_);
lean_ctor_set(v___x_1469_, 1, v___x_1466_);
lean_ctor_set(v___x_1469_, 2, v___x_1468_);
lean_ctor_set(v___x_1469_, 3, v___y_1406_);
lean_inc_ref(v___y_1410_);
lean_inc_n(v___y_1405_, 3);
v___x_1470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1460_);
lean_ctor_set(v___x_1470_, 1, v___y_1405_);
lean_ctor_set(v___x_1470_, 2, v___y_1410_);
v___x_1471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_1472_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1392_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_1474_ = l_Lean_Name_mkStr4(v___y_1383_, v___y_1393_, v___y_1392_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_1476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1460_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_1478_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Lean_addMacroScope(v___y_1397_, v___x_1479_, v___y_1380_);
lean_inc_ref_n(v___y_1381_, 2);
v___x_1481_ = l_Lean_Name_mkStr1(v___y_1381_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_inc_ref(v___y_1411_);
v___x_1483_ = l_Lean_Name_mkStr3(v___y_1383_, v___y_1393_, v___y_1411_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = l_Lean_Name_mkStr2(v___y_1383_, v___y_1393_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
v___x_1487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_1488_ = l_Lean_Name_mkStr2(v___y_1383_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
v___x_1490_ = l_Lean_Name_mkStr1(v___y_1383_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___y_1406_);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1489_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1486_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1484_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1482_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1497_, 0, v_a_1460_);
lean_ctor_set(v___x_1497_, 1, v___x_1478_);
lean_ctor_set(v___x_1497_, 2, v___x_1480_);
lean_ctor_set(v___x_1497_, 3, v___x_1496_);
v___x_1498_ = l_Lean_Syntax_node1(v_a_1460_, v___x_1477_, v___x_1497_);
v___x_1499_ = l_Lean_Syntax_node2(v_a_1460_, v___x_1474_, v___x_1476_, v___x_1498_);
v___x_1500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_1501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_1503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_1504_ = l_Lean_addMacroScope(v___y_1397_, v___x_1503_, v___y_1380_);
v___x_1505_ = l_Lean_Name_mkStr3(v___y_1381_, v___x_1501_, v___x_1502_);
lean_inc(v___y_1377_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___y_1377_);
v___x_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v___y_1406_);
v___x_1508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1508_, 0, v_a_1460_);
lean_ctor_set(v___x_1508_, 1, v___x_1500_);
lean_ctor_set(v___x_1508_, 2, v___x_1504_);
lean_ctor_set(v___x_1508_, 3, v___x_1507_);
lean_inc(v_type_1147_);
v___x_1509_ = l_Lean_Syntax_node1(v_a_1460_, v___y_1405_, v_type_1147_);
v___x_1510_ = l_Lean_Syntax_node2(v_a_1460_, v___y_1398_, v___x_1508_, v___x_1509_);
v___x_1511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_1512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_a_1460_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_Syntax_node3(v_a_1460_, v___x_1472_, v___x_1499_, v___x_1510_, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node1(v_a_1460_, v___y_1405_, v___x_1513_);
lean_inc(v___x_1463_);
v___x_1515_ = l_Lean_Syntax_node5(v_a_1460_, v___x_1463_, v_fields_1140_, v___x_1465_, v___x_1469_, v___x_1470_, v___x_1514_);
v_ref_1516_ = l_Lean_replaceRef(v___x_1515_, v___y_1386_);
lean_inc(v_ref_1516_);
lean_inc(v___y_1403_);
lean_inc(v___y_1385_);
lean_inc(v___y_1402_);
v___x_1517_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1402_);
lean_ctor_set(v___x_1517_, 1, v___y_1397_);
lean_ctor_set(v___x_1517_, 2, v___y_1380_);
lean_ctor_set(v___x_1517_, 3, v___y_1385_);
lean_ctor_set(v___x_1517_, 4, v___y_1403_);
lean_ctor_set(v___x_1517_, 5, v_ref_1516_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1138_, v_ref_1516_, v___x_1517_, v_a_1461_);
lean_dec_ref_known(v___x_1517_, 6);
lean_dec(v_ref_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_n(v_a_1519_, 29);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1518_, 2);
lean_inc(v___y_1389_);
lean_inc_n(v___y_1409_, 2);
v___x_1521_ = l_Lean_Syntax_node4(v___y_1409_, v___x_1443_, v___x_1444_, v___x_1452_, v___x_1456_, v___y_1389_);
v___x_1522_ = l_Lean_Syntax_node6(v___y_1409_, v___x_1418_, v___x_1421_, v___x_1422_, v___y_1389_, v___x_1424_, v___x_1441_, v___x_1521_);
lean_inc(v___y_1388_);
v___x_1523_ = l_Lean_Syntax_node2(v___y_1409_, v___y_1388_, v___x_1416_, v___x_1522_);
v___x_1524_ = lean_array_push(v___y_1394_, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1519_);
lean_ctor_set(v___x_1525_, 1, v___x_1464_);
v___x_1526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_1527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1380_, 6);
lean_inc_n(v___y_1397_, 6);
v___x_1528_ = l_Lean_addMacroScope(v___y_1397_, v___x_1527_, v___y_1380_);
lean_inc_n(v___y_1406_, 6);
v___x_1529_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1519_);
lean_ctor_set(v___x_1529_, 1, v___x_1526_);
lean_ctor_set(v___x_1529_, 2, v___x_1528_);
lean_ctor_set(v___x_1529_, 3, v___y_1406_);
lean_inc_ref(v___y_1410_);
lean_inc_n(v___y_1405_, 6);
v___x_1530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1519_);
lean_ctor_set(v___x_1530_, 1, v___y_1405_);
lean_ctor_set(v___x_1530_, 2, v___y_1410_);
lean_inc_ref(v___y_1379_);
v___x_1531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_a_1519_);
lean_ctor_set(v___x_1531_, 1, v___y_1379_);
v___x_1532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_1533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_1534_ = l_Lean_addMacroScope(v___y_1397_, v___x_1533_, v___y_1380_);
v___x_1535_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1519_);
lean_ctor_set(v___x_1535_, 1, v___x_1532_);
lean_ctor_set(v___x_1535_, 2, v___x_1534_);
lean_ctor_set(v___x_1535_, 3, v___y_1406_);
lean_inc_ref_n(v___x_1530_, 14);
lean_inc_n(v___y_1412_, 2);
v___x_1536_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1412_, v___x_1535_, v___x_1530_);
lean_inc_ref(v___y_1384_);
v___x_1537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1519_);
lean_ctor_set(v___x_1537_, 1, v___y_1384_);
lean_inc_ref(v___x_1537_);
lean_inc(v___y_1407_);
v___x_1538_ = l_Lean_Syntax_node3(v_a_1519_, v___y_1407_, v___x_1537_, v___x_1530_, v___y_1387_);
v___x_1539_ = l_Lean_Syntax_node3(v_a_1519_, v___y_1405_, v___x_1530_, v___x_1530_, v___x_1538_);
lean_inc(v___x_1539_);
lean_inc_n(v___y_1376_, 2);
v___x_1540_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1376_, v___x_1536_, v___x_1539_);
v___x_1541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_1543_ = l_Lean_addMacroScope(v___y_1397_, v___x_1542_, v___y_1380_);
v___x_1544_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1544_, 0, v_a_1519_);
lean_ctor_set(v___x_1544_, 1, v___x_1541_);
lean_ctor_set(v___x_1544_, 2, v___x_1543_);
lean_ctor_set(v___x_1544_, 3, v___y_1406_);
v___x_1545_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1412_, v___x_1544_, v___x_1530_);
v___x_1546_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1376_, v___x_1545_, v___x_1539_);
v___x_1547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_1549_ = l_Lean_addMacroScope(v___y_1397_, v___x_1548_, v___y_1380_);
v___x_1550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1550_, 0, v_a_1519_);
lean_ctor_set(v___x_1550_, 1, v___x_1547_);
lean_ctor_set(v___x_1550_, 2, v___x_1549_);
lean_ctor_set(v___x_1550_, 3, v___y_1406_);
v___x_1551_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1412_, v___x_1550_, v___x_1530_);
v___x_1552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_1554_ = l_Lean_addMacroScope(v___y_1397_, v___x_1553_, v___y_1380_);
v___x_1555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_1377_, 2);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___y_1377_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___y_1406_);
v___x_1558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1519_);
lean_ctor_set(v___x_1558_, 1, v___x_1552_);
lean_ctor_set(v___x_1558_, 2, v___x_1554_);
lean_ctor_set(v___x_1558_, 3, v___x_1557_);
v___x_1559_ = l_Lean_Syntax_node3(v_a_1519_, v___y_1407_, v___x_1537_, v___x_1530_, v___x_1558_);
v___x_1560_ = l_Lean_Syntax_node3(v_a_1519_, v___y_1405_, v___x_1530_, v___x_1530_, v___x_1559_);
v___x_1561_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1376_, v___x_1551_, v___x_1560_);
v___x_1562_ = l_Lean_Syntax_node6(v_a_1519_, v___y_1405_, v___x_1540_, v___x_1530_, v___x_1546_, v___x_1530_, v___x_1561_, v___x_1530_);
v___x_1563_ = l_Lean_Syntax_node1(v_a_1519_, v___y_1400_, v___x_1562_);
v___x_1564_ = l_Lean_Syntax_node1(v_a_1519_, v___y_1404_, v___x_1530_);
lean_inc_ref(v___y_1382_);
v___x_1565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1519_);
lean_ctor_set(v___x_1565_, 1, v___y_1382_);
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_1567_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_1568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_1569_ = l_Lean_addMacroScope(v___y_1397_, v___x_1568_, v___y_1380_);
lean_inc_ref(v___y_1381_);
v___x_1570_ = l_Lean_Name_mkStr2(v___y_1381_, v___x_1566_);
lean_inc(v___x_1570_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___y_1377_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___y_1406_);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1575_, 0, v_a_1519_);
lean_ctor_set(v___x_1575_, 1, v___x_1567_);
lean_ctor_set(v___x_1575_, 2, v___x_1569_);
lean_ctor_set(v___x_1575_, 3, v___x_1574_);
v___x_1576_ = l_Lean_Syntax_node2(v_a_1519_, v___y_1405_, v___x_1565_, v___x_1575_);
lean_inc_ref(v___y_1391_);
v___x_1577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1519_);
lean_ctor_set(v___x_1577_, 1, v___y_1391_);
v___x_1578_ = l_Lean_Syntax_node6(v_a_1519_, v___y_1396_, v___x_1531_, v___x_1530_, v___x_1563_, v___x_1564_, v___x_1576_, v___x_1577_);
v___x_1579_ = l_Lean_Syntax_node1(v_a_1519_, v___y_1405_, v___x_1578_);
v___x_1580_ = l_Lean_Syntax_node5(v_a_1519_, v___x_1463_, v___x_1515_, v___x_1525_, v___x_1529_, v___x_1530_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1524_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v_a_1129_ = v___x_1581_;
v_a_1130_ = v_a_1520_;
goto v___jp_1128_;
}
else
{
lean_object* v_a_1582_; lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v___x_1515_);
lean_dec(v___x_1463_);
lean_dec(v___x_1456_);
lean_dec(v___x_1452_);
lean_dec_ref_known(v___x_1444_, 2);
lean_dec(v___x_1443_);
lean_dec(v___x_1441_);
lean_dec(v___x_1424_);
lean_dec_ref_known(v___x_1422_, 2);
lean_dec(v___x_1421_);
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v___y_1412_);
lean_dec(v___y_1409_);
lean_dec(v___y_1407_);
lean_dec(v___y_1404_);
lean_dec(v___y_1400_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1389_);
lean_dec(v___y_1387_);
lean_dec(v___y_1376_);
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v_a_1582_ = lean_ctor_get(v___x_1518_, 0);
v_a_1583_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1518_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_inc(v_a_1582_);
lean_dec(v___x_1518_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1582_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v___x_1456_);
lean_dec(v___x_1452_);
lean_dec_ref_known(v___x_1444_, 2);
lean_dec(v___x_1443_);
lean_dec(v___x_1441_);
lean_dec(v___x_1424_);
lean_dec_ref_known(v___x_1422_, 2);
lean_dec(v___x_1421_);
lean_dec(v___x_1418_);
lean_dec(v___x_1416_);
lean_dec(v___y_1412_);
lean_dec(v___y_1409_);
lean_dec(v___y_1407_);
lean_dec(v___y_1404_);
lean_dec(v___y_1400_);
lean_dec(v___y_1398_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1389_);
lean_dec(v___y_1387_);
lean_dec(v___y_1376_);
lean_dec(v_fields_1140_);
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v_a_1591_ = lean_ctor_get(v___x_1459_, 0);
v_a_1592_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1459_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_inc(v_a_1591_);
lean_dec(v___x_1459_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1138_, v___y_1611_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_n(v_a_1636_, 2);
v_a_1637_ = lean_ctor_get(v___x_1635_, 1);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1635_, 2);
v___x_1638_ = l_Lean_mkIdentFrom(v_id_1145_, v___y_1634_, v___x_1138_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1629_);
v___x_1639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1636_);
lean_ctor_set(v___x_1639_, 1, v___y_1629_);
lean_ctor_set(v___x_1639_, 2, v___y_1631_);
if (lean_obj_tag(v_vis_x3f_1120_) == 1)
{
lean_object* v_val_1640_; lean_object* v___x_1641_; 
v_val_1640_ = lean_ctor_get(v_vis_x3f_1120_, 0);
lean_inc(v_val_1640_);
v___x_1641_ = l_Array_mkArray1___redArg(v_val_1640_);
v___y_1376_ = v___y_1601_;
v___y_1377_ = v___y_1602_;
v___y_1378_ = v___y_1603_;
v___y_1379_ = v___y_1606_;
v___y_1380_ = v___y_1605_;
v___y_1381_ = v___y_1604_;
v___y_1382_ = v___y_1608_;
v___y_1383_ = v___y_1607_;
v___y_1384_ = v___y_1609_;
v___y_1385_ = v___y_1610_;
v___y_1386_ = v___y_1611_;
v___y_1387_ = v___y_1612_;
v___y_1388_ = v___y_1613_;
v___y_1389_ = v___x_1639_;
v___y_1390_ = v_a_1637_;
v___y_1391_ = v___y_1614_;
v___y_1392_ = v___y_1615_;
v___y_1393_ = v___y_1616_;
v___y_1394_ = v___y_1617_;
v___y_1395_ = v___y_1618_;
v___y_1396_ = v___y_1619_;
v___y_1397_ = v___y_1620_;
v___y_1398_ = v___y_1621_;
v___y_1399_ = v___y_1622_;
v___y_1400_ = v___y_1624_;
v___y_1401_ = v___y_1623_;
v___y_1402_ = v___y_1626_;
v___y_1403_ = v___y_1625_;
v___y_1404_ = v___y_1628_;
v___y_1405_ = v___y_1629_;
v___y_1406_ = v___y_1627_;
v___y_1407_ = v___y_1630_;
v___y_1408_ = v___x_1638_;
v___y_1409_ = v_a_1636_;
v___y_1410_ = v___y_1631_;
v___y_1411_ = v___y_1632_;
v___y_1412_ = v___y_1633_;
v___y_1413_ = v___x_1641_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1376_ = v___y_1601_;
v___y_1377_ = v___y_1602_;
v___y_1378_ = v___y_1603_;
v___y_1379_ = v___y_1606_;
v___y_1380_ = v___y_1605_;
v___y_1381_ = v___y_1604_;
v___y_1382_ = v___y_1608_;
v___y_1383_ = v___y_1607_;
v___y_1384_ = v___y_1609_;
v___y_1385_ = v___y_1610_;
v___y_1386_ = v___y_1611_;
v___y_1387_ = v___y_1612_;
v___y_1388_ = v___y_1613_;
v___y_1389_ = v___x_1639_;
v___y_1390_ = v_a_1637_;
v___y_1391_ = v___y_1614_;
v___y_1392_ = v___y_1615_;
v___y_1393_ = v___y_1616_;
v___y_1394_ = v___y_1617_;
v___y_1395_ = v___y_1618_;
v___y_1396_ = v___y_1619_;
v___y_1397_ = v___y_1620_;
v___y_1398_ = v___y_1621_;
v___y_1399_ = v___y_1622_;
v___y_1400_ = v___y_1624_;
v___y_1401_ = v___y_1623_;
v___y_1402_ = v___y_1626_;
v___y_1403_ = v___y_1625_;
v___y_1404_ = v___y_1628_;
v___y_1405_ = v___y_1629_;
v___y_1406_ = v___y_1627_;
v___y_1407_ = v___y_1630_;
v___y_1408_ = v___x_1638_;
v___y_1409_ = v_a_1636_;
v___y_1410_ = v___y_1631_;
v___y_1411_ = v___y_1632_;
v___y_1412_ = v___y_1633_;
v___y_1413_ = v___x_1642_;
goto v___jp_1375_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec(v___y_1630_);
lean_dec(v___y_1628_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1612_);
lean_dec(v___y_1601_);
lean_dec(v_fields_1140_);
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v_a_1643_ = lean_ctor_get(v___x_1635_, 0);
v_a_1644_ = lean_ctor_get(v___x_1635_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1635_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_inc(v_a_1643_);
lean_dec(v___x_1635_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1643_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
v___jp_1653_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_inc_ref_n(v___y_1667_, 2);
v___x_1671_ = l_Array_append___redArg(v___y_1667_, v___y_1670_);
lean_dec_ref(v___y_1670_);
lean_inc_n(v___y_1660_, 19);
lean_inc_n(v___y_1654_, 69);
v___x_1672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1654_);
lean_ctor_set(v___x_1672_, 1, v___y_1660_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_inc_n(v___y_1665_, 35);
lean_inc(v___y_1656_);
v___x_1673_ = l_Lean_Syntax_node7(v___y_1654_, v___y_1656_, v___y_1665_, v___y_1665_, v___x_1672_, v___y_1665_, v___y_1665_, v___y_1665_, v___y_1665_);
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_1668_, 4);
lean_inc_ref_n(v___y_1666_, 15);
lean_inc_ref_n(v___y_1661_, 15);
v___x_1675_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___y_1668_, v___x_1674_);
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_1677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1654_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_1679_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___y_1668_, v___x_1678_);
lean_inc(v___y_1669_);
lean_inc(v___x_1679_);
v___x_1680_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1679_, v___y_1669_, v___y_1665_);
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_1682_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___y_1668_, v___x_1681_);
v___x_1683_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_1684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_1685_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1684_);
v___x_1686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___y_1654_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_1689_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1688_);
v___x_1690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_1691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_1659_, 8);
lean_inc_n(v___y_1655_, 8);
v___x_1692_ = l_Lean_addMacroScope(v___y_1655_, v___x_1691_, v___y_1659_);
v___x_1693_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_1694_ = lean_box(0);
v___x_1695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_1696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1696_, 0, v___y_1654_);
lean_ctor_set(v___x_1696_, 1, v___x_1690_);
lean_ctor_set(v___x_1696_, 2, v___x_1692_);
lean_ctor_set(v___x_1696_, 3, v___x_1695_);
lean_inc(v_type_1147_);
lean_inc(v_structTy_1118_);
v___x_1697_ = l_Lean_Syntax_node2(v___y_1654_, v___y_1660_, v_structTy_1118_, v_type_1147_);
lean_inc_n(v___x_1689_, 2);
v___x_1698_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1689_, v___x_1696_, v___x_1697_);
lean_inc(v___x_1685_);
v___x_1699_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1685_, v___x_1687_, v___x_1698_);
v___x_1700_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1699_);
v___x_1701_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1682_, v___y_1665_, v___x_1700_);
v___x_1702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_1703_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___y_1668_, v___x_1702_);
v___x_1704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1654_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_1707_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1706_);
v___x_1708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_1709_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1708_);
v___x_1710_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_1711_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1710_);
v___x_1712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_1713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_1714_ = l_Lean_addMacroScope(v___y_1655_, v___x_1713_, v___y_1659_);
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_1716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1716_, 0, v___y_1654_);
lean_ctor_set(v___x_1716_, 1, v___x_1712_);
lean_ctor_set(v___x_1716_, 2, v___x_1714_);
lean_ctor_set(v___x_1716_, 3, v___x_1715_);
lean_inc_n(v___x_1711_, 5);
v___x_1717_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1711_, v___x_1716_, v___y_1665_);
v___x_1718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_1720_ = l_Lean_addMacroScope(v___y_1655_, v___x_1719_, v___y_1659_);
v___x_1721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1654_);
lean_ctor_set(v___x_1721_, 1, v___x_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
lean_ctor_set(v___x_1721_, 3, v___x_1694_);
lean_inc_ref_n(v___x_1721_, 3);
v___x_1722_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1721_);
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_1724_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1723_);
v___x_1725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1654_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_1728_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1727_);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_1730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___y_1654_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
lean_inc_n(v_id_1145_, 3);
v___x_1731_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1728_, v___x_1721_, v___x_1730_, v_id_1145_);
lean_inc(v___x_1731_);
lean_inc_ref_n(v___x_1726_, 5);
lean_inc_n(v___x_1724_, 6);
v___x_1732_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1731_);
lean_inc(v___x_1722_);
v___x_1733_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___x_1722_, v___y_1665_, v___x_1732_);
lean_inc_n(v___x_1709_, 6);
v___x_1734_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1717_, v___x_1733_);
v___x_1735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_1736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_1737_ = l_Lean_addMacroScope(v___y_1655_, v___x_1736_, v___y_1659_);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_1739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1654_);
lean_ctor_set(v___x_1739_, 1, v___x_1735_);
lean_ctor_set(v___x_1739_, 2, v___x_1737_);
lean_ctor_set(v___x_1739_, 3, v___x_1738_);
v___x_1740_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1711_, v___x_1739_, v___y_1665_);
v___x_1741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_1742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_1743_ = l_Lean_addMacroScope(v___y_1655_, v___x_1742_, v___y_1659_);
v___x_1744_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1744_, 0, v___y_1654_);
lean_ctor_set(v___x_1744_, 1, v___x_1741_);
lean_ctor_set(v___x_1744_, 2, v___x_1743_);
lean_ctor_set(v___x_1744_, 3, v___x_1694_);
lean_inc_ref(v___x_1744_);
v___x_1745_ = l_Lean_Syntax_node2(v___y_1654_, v___y_1660_, v___x_1744_, v___x_1721_);
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_1747_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1746_);
v___x_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_1749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___y_1654_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1654_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_Syntax_node2(v___y_1654_, v___y_1660_, v___x_1722_, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = l_Lean_SourceInfo_fromRef(v___x_1753_, v___x_1138_);
lean_inc(v___x_1754_);
v___x_1755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___y_1660_);
lean_ctor_set(v___x_1755_, 2, v___y_1667_);
v___x_1756_ = l_Lean_Syntax_node2(v___x_1754_, v___x_1711_, v_id_1145_, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1744_);
v___x_1758_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___y_1665_, v___y_1665_, v___x_1757_);
lean_inc(v___x_1756_);
v___x_1759_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1756_, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1759_);
lean_inc_n(v___x_1707_, 3);
v___x_1761_ = l_Lean_Syntax_node1(v___y_1654_, v___x_1707_, v___x_1760_);
v___x_1762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_1763_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1762_);
lean_inc(v___x_1763_);
v___x_1764_ = l_Lean_Syntax_node1(v___y_1654_, v___x_1763_, v___y_1665_);
v___x_1765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1654_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
lean_inc_ref(v___x_1766_);
lean_inc(v___x_1764_);
lean_inc(v___x_1752_);
lean_inc_ref(v___x_1749_);
lean_inc_n(v___x_1747_, 2);
v___x_1767_ = l_Lean_Syntax_node6(v___y_1654_, v___x_1747_, v___x_1749_, v___x_1752_, v___x_1761_, v___x_1764_, v___y_1665_, v___x_1766_);
v___x_1768_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1767_);
v___x_1769_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___x_1745_, v___y_1665_, v___x_1768_);
v___x_1770_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1740_, v___x_1769_);
v___x_1771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_1773_ = l_Lean_addMacroScope(v___y_1655_, v___x_1772_, v___y_1659_);
v___x_1774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_1775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1775_, 0, v___y_1654_);
lean_ctor_set(v___x_1775_, 1, v___x_1771_);
lean_ctor_set(v___x_1775_, 2, v___x_1773_);
lean_ctor_set(v___x_1775_, 3, v___x_1774_);
v___x_1776_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1711_, v___x_1775_, v___y_1665_);
v___x_1777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_1778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_1779_ = l_Lean_addMacroScope(v___y_1655_, v___x_1778_, v___y_1659_);
v___x_1780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1654_);
lean_ctor_set(v___x_1780_, 1, v___x_1777_);
lean_ctor_set(v___x_1780_, 2, v___x_1779_);
lean_ctor_set(v___x_1780_, 3, v___x_1694_);
lean_inc_ref(v___x_1780_);
v___x_1781_ = l_Lean_Syntax_node2(v___y_1654_, v___y_1660_, v___x_1780_, v___x_1721_);
v___x_1782_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1731_);
v___x_1783_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1689_, v___x_1780_, v___x_1782_);
v___x_1784_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1783_);
v___x_1785_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___y_1665_, v___y_1665_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1756_, v___x_1785_);
v___x_1787_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1786_);
v___x_1788_ = l_Lean_Syntax_node1(v___y_1654_, v___x_1707_, v___x_1787_);
v___x_1789_ = l_Lean_Syntax_node6(v___y_1654_, v___x_1747_, v___x_1749_, v___x_1752_, v___x_1788_, v___x_1764_, v___y_1665_, v___x_1766_);
v___x_1790_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1789_);
v___x_1791_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___x_1781_, v___y_1665_, v___x_1790_);
v___x_1792_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1776_, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_1794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_1795_ = l_Lean_addMacroScope(v___y_1655_, v___x_1794_, v___y_1659_);
v___x_1796_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1796_, 0, v___y_1654_);
lean_ctor_set(v___x_1796_, 1, v___x_1793_);
lean_ctor_set(v___x_1796_, 2, v___x_1795_);
lean_ctor_set(v___x_1796_, 3, v___x_1694_);
v___x_1797_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1711_, v___x_1796_, v___y_1665_);
v___x_1798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_1799_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___y_1654_);
lean_ctor_set(v___x_1800_, 1, v___x_1798_);
v___x_1801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_1802_ = l_Lean_Name_mkStr4(v___y_1661_, v___y_1666_, v___x_1683_, v___x_1801_);
lean_inc(v___x_1119_);
v___x_1803_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1660_, v___x_1119_);
v___x_1804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1654_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
lean_inc(v_defVal_1148_);
v___x_1806_ = l_Lean_Syntax_node4(v___y_1654_, v___x_1802_, v___x_1803_, v___y_1665_, v___x_1805_, v_defVal_1148_);
v___x_1807_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1799_, v___x_1800_, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1724_, v___x_1726_, v___y_1665_, v___x_1807_);
v___x_1809_ = l_Lean_Syntax_node3(v___y_1654_, v___y_1660_, v___y_1665_, v___y_1665_, v___x_1808_);
v___x_1810_ = l_Lean_Syntax_node2(v___y_1654_, v___x_1709_, v___x_1797_, v___x_1809_);
v___x_1811_ = l_Lean_Syntax_node7(v___y_1654_, v___y_1660_, v___x_1734_, v___y_1665_, v___x_1770_, v___y_1665_, v___x_1792_, v___y_1665_, v___x_1810_);
v___x_1812_ = l_Lean_Syntax_node1(v___y_1654_, v___x_1707_, v___x_1811_);
v___x_1813_ = l_Lean_Syntax_node3(v___y_1654_, v___x_1703_, v___x_1705_, v___x_1812_, v___y_1665_);
v___x_1814_ = l_Lean_Syntax_node5(v___y_1654_, v___x_1675_, v___x_1677_, v___x_1680_, v___x_1701_, v___x_1813_, v___y_1665_);
lean_inc(v___y_1664_);
v___x_1815_ = l_Lean_Syntax_node2(v___y_1654_, v___y_1664_, v___x_1673_, v___x_1814_);
v___x_1816_ = lean_array_push(v_cmds_1139_, v___x_1815_);
lean_inc(v___x_1652_);
v___x_1817_ = l_Lake_Name_quoteFrom(v_id_1145_, v___x_1652_, v___x_1138_);
if (v_parent_1149_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
lean_dec(v___x_1652_);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_array_get_size(v_ids_1146_);
v___x_1820_ = lean_nat_dec_lt(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec(v___x_1817_);
lean_dec(v___x_1763_);
lean_dec(v___x_1747_);
lean_dec(v___x_1724_);
lean_dec(v___x_1711_);
lean_dec(v___x_1709_);
lean_dec(v___x_1707_);
lean_dec(v___x_1689_);
lean_dec(v___x_1685_);
lean_dec(v___x_1679_);
lean_dec(v___y_1669_);
lean_del_object(v___x_1142_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v_fields_1140_);
v_a_1129_ = v___x_1821_;
v_a_1130_ = v___y_1127_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1822_ = lean_array_fget_borrowed(v_ids_1146_, v___x_1818_);
v___x_1823_ = l_Lean_TSyntax_getId(v___x_1822_);
lean_inc(v___x_1823_);
lean_inc(v___x_1822_);
v___x_1824_ = l_Lake_Name_quoteFrom(v___x_1822_, v___x_1823_, v___x_1138_);
v___x_1825_ = l_Lean_Name_hasMacroScopes(v___x_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1121_, v___x_1823_);
lean_inc(v___x_1822_);
v___y_1320_ = v___x_1709_;
v___y_1321_ = v___x_1694_;
v___y_1322_ = v___y_1656_;
v___y_1323_ = v___x_1818_;
v___y_1324_ = v___x_1693_;
v___y_1325_ = v___y_1659_;
v___y_1326_ = v___x_1748_;
v___y_1327_ = v___y_1661_;
v___y_1328_ = v___x_1686_;
v___y_1329_ = v___x_1725_;
v___y_1330_ = v___y_1662_;
v___y_1331_ = v___y_1663_;
v___y_1332_ = v___x_1824_;
v___y_1333_ = v___x_1817_;
v___y_1334_ = v___y_1664_;
v___y_1335_ = v___x_1765_;
v___y_1336_ = v___x_1683_;
v___y_1337_ = v___y_1666_;
v___y_1338_ = v___x_1816_;
v___y_1339_ = v___y_1669_;
v___y_1340_ = v___x_1747_;
v___y_1341_ = v___x_1685_;
v___y_1342_ = v___y_1655_;
v___y_1343_ = v___x_1689_;
v___y_1344_ = v___x_1679_;
v___y_1345_ = v___x_1707_;
v___y_1346_ = v___y_1657_;
v___y_1347_ = v___y_1658_;
v___y_1348_ = v___x_1694_;
v___y_1349_ = v___x_1763_;
v___y_1350_ = v___y_1660_;
v___y_1351_ = v___x_1724_;
v___y_1352_ = v___x_1819_;
v___y_1353_ = v___y_1667_;
v___y_1354_ = v___x_1822_;
v___y_1355_ = v___y_1668_;
v___y_1356_ = v___x_1711_;
v___y_1357_ = v___x_1826_;
goto v___jp_1319_;
}
else
{
lean_object* v_view_1827_; lean_object* v_name_1828_; lean_object* v_imported_1829_; lean_object* v_ctx_1830_; lean_object* v_scopes_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1840_; 
v_view_1827_ = l_Lean_extractMacroScopes(v___x_1823_);
v_name_1828_ = lean_ctor_get(v_view_1827_, 0);
v_imported_1829_ = lean_ctor_get(v_view_1827_, 1);
v_ctx_1830_ = lean_ctor_get(v_view_1827_, 2);
v_scopes_1831_ = lean_ctor_get(v_view_1827_, 3);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_view_1827_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1833_ = v_view_1827_;
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_scopes_1831_);
lean_inc(v_ctx_1830_);
lean_inc(v_imported_1829_);
lean_inc(v_name_1828_);
lean_dec(v_view_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1121_, v_name_1828_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_imported_1829_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_ctx_1830_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_scopes_1831_);
v___x_1837_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_MacroScopesView_review(v___x_1837_);
lean_inc(v___x_1822_);
v___y_1320_ = v___x_1709_;
v___y_1321_ = v___x_1694_;
v___y_1322_ = v___y_1656_;
v___y_1323_ = v___x_1818_;
v___y_1324_ = v___x_1693_;
v___y_1325_ = v___y_1659_;
v___y_1326_ = v___x_1748_;
v___y_1327_ = v___y_1661_;
v___y_1328_ = v___x_1686_;
v___y_1329_ = v___x_1725_;
v___y_1330_ = v___y_1662_;
v___y_1331_ = v___y_1663_;
v___y_1332_ = v___x_1824_;
v___y_1333_ = v___x_1817_;
v___y_1334_ = v___y_1664_;
v___y_1335_ = v___x_1765_;
v___y_1336_ = v___x_1683_;
v___y_1337_ = v___y_1666_;
v___y_1338_ = v___x_1816_;
v___y_1339_ = v___y_1669_;
v___y_1340_ = v___x_1747_;
v___y_1341_ = v___x_1685_;
v___y_1342_ = v___y_1655_;
v___y_1343_ = v___x_1689_;
v___y_1344_ = v___x_1679_;
v___y_1345_ = v___x_1707_;
v___y_1346_ = v___y_1657_;
v___y_1347_ = v___y_1658_;
v___y_1348_ = v___x_1694_;
v___y_1349_ = v___x_1763_;
v___y_1350_ = v___y_1660_;
v___y_1351_ = v___x_1724_;
v___y_1352_ = v___x_1819_;
v___y_1353_ = v___y_1667_;
v___y_1354_ = v___x_1822_;
v___y_1355_ = v___y_1668_;
v___y_1356_ = v___x_1711_;
v___y_1357_ = v___x_1838_;
goto v___jp_1319_;
}
}
}
}
}
else
{
uint8_t v___x_1841_; 
lean_del_object(v___x_1142_);
v___x_1841_ = l_Lean_Name_hasMacroScopes(v___x_1652_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1121_, v___x_1652_);
v___y_1601_ = v___x_1709_;
v___y_1602_ = v___x_1694_;
v___y_1603_ = v___y_1656_;
v___y_1604_ = v___x_1693_;
v___y_1605_ = v___y_1659_;
v___y_1606_ = v___x_1748_;
v___y_1607_ = v___y_1661_;
v___y_1608_ = v___x_1686_;
v___y_1609_ = v___x_1725_;
v___y_1610_ = v___y_1662_;
v___y_1611_ = v___y_1663_;
v___y_1612_ = v___x_1817_;
v___y_1613_ = v___y_1664_;
v___y_1614_ = v___x_1765_;
v___y_1615_ = v___x_1683_;
v___y_1616_ = v___y_1666_;
v___y_1617_ = v___x_1816_;
v___y_1618_ = v___y_1669_;
v___y_1619_ = v___x_1747_;
v___y_1620_ = v___y_1655_;
v___y_1621_ = v___x_1689_;
v___y_1622_ = v___x_1685_;
v___y_1623_ = v___x_1679_;
v___y_1624_ = v___x_1707_;
v___y_1625_ = v___y_1658_;
v___y_1626_ = v___y_1657_;
v___y_1627_ = v___x_1694_;
v___y_1628_ = v___x_1763_;
v___y_1629_ = v___y_1660_;
v___y_1630_ = v___x_1724_;
v___y_1631_ = v___y_1667_;
v___y_1632_ = v___y_1668_;
v___y_1633_ = v___x_1711_;
v___y_1634_ = v___x_1842_;
goto v___jp_1600_;
}
else
{
lean_object* v_view_1843_; lean_object* v_name_1844_; lean_object* v_imported_1845_; lean_object* v_ctx_1846_; lean_object* v_scopes_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_view_1843_ = l_Lean_extractMacroScopes(v___x_1652_);
v_name_1844_ = lean_ctor_get(v_view_1843_, 0);
v_imported_1845_ = lean_ctor_get(v_view_1843_, 1);
v_ctx_1846_ = lean_ctor_get(v_view_1843_, 2);
v_scopes_1847_ = lean_ctor_get(v_view_1843_, 3);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_view_1843_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v_view_1843_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_scopes_1847_);
lean_inc(v_ctx_1846_);
lean_inc(v_imported_1845_);
lean_inc(v_name_1844_);
lean_dec(v_view_1843_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1121_, v_name_1844_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_imported_1845_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_ctx_1846_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_scopes_1847_);
v___x_1853_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_MacroScopesView_review(v___x_1853_);
v___y_1601_ = v___x_1709_;
v___y_1602_ = v___x_1694_;
v___y_1603_ = v___y_1656_;
v___y_1604_ = v___x_1693_;
v___y_1605_ = v___y_1659_;
v___y_1606_ = v___x_1748_;
v___y_1607_ = v___y_1661_;
v___y_1608_ = v___x_1686_;
v___y_1609_ = v___x_1725_;
v___y_1610_ = v___y_1662_;
v___y_1611_ = v___y_1663_;
v___y_1612_ = v___x_1817_;
v___y_1613_ = v___y_1664_;
v___y_1614_ = v___x_1765_;
v___y_1615_ = v___x_1683_;
v___y_1616_ = v___y_1666_;
v___y_1617_ = v___x_1816_;
v___y_1618_ = v___y_1669_;
v___y_1619_ = v___x_1747_;
v___y_1620_ = v___y_1655_;
v___y_1621_ = v___x_1689_;
v___y_1622_ = v___x_1685_;
v___y_1623_ = v___x_1679_;
v___y_1624_ = v___x_1707_;
v___y_1625_ = v___y_1658_;
v___y_1626_ = v___y_1657_;
v___y_1627_ = v___x_1694_;
v___y_1628_ = v___x_1763_;
v___y_1629_ = v___y_1660_;
v___y_1630_ = v___x_1724_;
v___y_1631_ = v___y_1667_;
v___y_1632_ = v___y_1668_;
v___y_1633_ = v___x_1711_;
v___y_1634_ = v___x_1854_;
goto v___jp_1600_;
}
}
}
}
}
v___jp_1857_:
{
lean_object* v_methods_1859_; lean_object* v_quotContext_1860_; lean_object* v_currMacroScope_1861_; lean_object* v_currRecDepth_1862_; lean_object* v_maxRecDepth_1863_; lean_object* v_ref_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_methods_1859_ = lean_ctor_get(v___y_1126_, 0);
v_quotContext_1860_ = lean_ctor_get(v___y_1126_, 1);
v_currMacroScope_1861_ = lean_ctor_get(v___y_1126_, 2);
v_currRecDepth_1862_ = lean_ctor_get(v___y_1126_, 3);
v_maxRecDepth_1863_ = lean_ctor_get(v___y_1126_, 4);
v_ref_1864_ = lean_ctor_get(v___y_1126_, 5);
v___x_1865_ = l_Lean_mkIdentFrom(v_id_1145_, v___y_1858_, v___x_1138_);
v___x_1866_ = l_Lean_SourceInfo_fromRef(v_ref_1864_, v___x_1138_);
v___x_1867_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_1868_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_1869_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_1870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_1871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_1872_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_1873_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_1866_);
v___x_1874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1866_);
lean_ctor_set(v___x_1874_, 1, v___x_1872_);
lean_ctor_set(v___x_1874_, 2, v___x_1873_);
if (lean_obj_tag(v_vis_x3f_1120_) == 1)
{
lean_object* v_val_1875_; lean_object* v___x_1876_; 
v_val_1875_ = lean_ctor_get(v_vis_x3f_1120_, 0);
lean_inc(v_val_1875_);
v___x_1876_ = l_Array_mkArray1___redArg(v_val_1875_);
v___y_1654_ = v___x_1866_;
v___y_1655_ = v_quotContext_1860_;
v___y_1656_ = v___x_1871_;
v___y_1657_ = v_methods_1859_;
v___y_1658_ = v_maxRecDepth_1863_;
v___y_1659_ = v_currMacroScope_1861_;
v___y_1660_ = v___x_1872_;
v___y_1661_ = v___x_1867_;
v___y_1662_ = v_currRecDepth_1862_;
v___y_1663_ = v_ref_1864_;
v___y_1664_ = v___x_1870_;
v___y_1665_ = v___x_1874_;
v___y_1666_ = v___x_1868_;
v___y_1667_ = v___x_1873_;
v___y_1668_ = v___x_1869_;
v___y_1669_ = v___x_1865_;
v___y_1670_ = v___x_1876_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1877_; 
v___x_1877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_1654_ = v___x_1866_;
v___y_1655_ = v_quotContext_1860_;
v___y_1656_ = v___x_1871_;
v___y_1657_ = v_methods_1859_;
v___y_1658_ = v_maxRecDepth_1863_;
v___y_1659_ = v_currMacroScope_1861_;
v___y_1660_ = v___x_1872_;
v___y_1661_ = v___x_1867_;
v___y_1662_ = v_currRecDepth_1862_;
v___y_1663_ = v_ref_1864_;
v___y_1664_ = v___x_1870_;
v___y_1665_ = v___x_1874_;
v___y_1666_ = v___x_1868_;
v___y_1667_ = v___x_1873_;
v___y_1668_ = v___x_1869_;
v___y_1669_ = v___x_1865_;
v___y_1670_ = v___x_1877_;
goto v___jp_1653_;
}
}
}
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_b_1125_);
lean_ctor_set(v___x_1895_, 1, v___y_1127_);
return v___x_1895_;
}
v___jp_1128_:
{
size_t v___x_1131_; size_t v___x_1132_; 
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_add(v_i_1123_, v___x_1131_);
v_i_1123_ = v___x_1132_;
v_b_1125_ = v_a_1129_;
v___y_1127_ = v_a_1130_;
goto _start;
}
v___jp_1134_:
{
if (lean_obj_tag(v___y_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v_a_1137_; 
v_a_1136_ = lean_ctor_get(v___y_1135_, 0);
lean_inc(v_a_1136_);
v_a_1137_ = lean_ctor_get(v___y_1135_, 1);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___y_1135_, 2);
v_a_1129_ = v_a_1136_;
v_a_1130_ = v_a_1137_;
goto v___jp_1128_;
}
else
{
lean_dec(v_vis_x3f_1120_);
lean_dec(v___x_1119_);
lean_dec(v_structTy_1118_);
return v___y_1135_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_structTy_1118_ = stack[0].m_obj;
lean_object* v___x_1119_ = stack[1].m_obj;
lean_object* v_vis_x3f_1120_ = stack[2].m_obj;
lean_object* v_structId_1121_ = stack[3].m_obj;
lean_object* v_as_1122_ = stack[4].m_obj;
size_t v_i_1123_ = stack[5].m_num;
size_t v_stop_1124_ = stack[6].m_num;
lean_object* v_b_1125_ = stack[7].m_obj;
lean_object* v___y_1126_ = stack[8].m_obj;
lean_object* v___y_1127_ = stack[9].m_obj;
lean_object* v_res_1896_;
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1118_, v___x_1119_, v_vis_x3f_1120_, v_structId_1121_, v_as_1122_, v_i_1123_, v_stop_1124_, v_b_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___boxed(lean_object* v_structTy_1897_, lean_object* v___x_1898_, lean_object* v_vis_x3f_1899_, lean_object* v_structId_1900_, lean_object* v_as_1901_, lean_object* v_i_1902_, lean_object* v_stop_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
size_t v_i_boxed_1907_; size_t v_stop_boxed_1908_; lean_object* v_res_1909_; 
v_i_boxed_1907_ = lean_unbox_usize(v_i_1902_);
lean_dec(v_i_1902_);
v_stop_boxed_1908_ = lean_unbox_usize(v_stop_1903_);
lean_dec(v_stop_1903_);
v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1897_, v___x_1898_, v_vis_x3f_1899_, v_structId_1900_, v_as_1901_, v_i_boxed_1907_, v_stop_boxed_1908_, v_b_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_as_1901_);
lean_dec(v_structId_1900_);
return v_res_1909_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(lean_object* v_structTy_1910_, lean_object* v___x_1911_, lean_object* v_vis_x3f_1912_, lean_object* v_structId_1913_, lean_object* v_as_1914_, size_t v_i_1915_, size_t v_stop_1916_, lean_object* v_b_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___y_1927_; uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_eq(v_i_1915_, v_stop_1916_);
if (v___x_1930_ == 0)
{
lean_object* v_cmds_1931_; lean_object* v_fields_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2686_; 
v_cmds_1931_ = lean_ctor_get(v_b_1917_, 0);
v_fields_1932_ = lean_ctor_get(v_b_1917_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_b_1917_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_1934_ = v_b_1917_;
v_isShared_1935_ = v_isSharedCheck_2686_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_fields_1932_);
lean_inc(v_cmds_1931_);
lean_dec(v_b_1917_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2686_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v_id_1937_; lean_object* v_ids_1938_; lean_object* v_type_1939_; lean_object* v_defVal_1940_; uint8_t v_parent_1941_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___x_2444_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2650_; uint8_t v___x_2670_; 
v___x_1936_ = lean_array_uget_borrowed(v_as_1914_, v_i_1915_);
v_id_1937_ = lean_ctor_get(v___x_1936_, 2);
v_ids_1938_ = lean_ctor_get(v___x_1936_, 3);
v_type_1939_ = lean_ctor_get(v___x_1936_, 4);
v_defVal_1940_ = lean_ctor_get(v___x_1936_, 5);
v_parent_1941_ = lean_ctor_get_uint8(v___x_1936_, sizeof(void*)*7);
v___x_2444_ = l_Lean_TSyntax_getId(v_id_1937_);
v___x_2670_ = l_Lean_Name_hasMacroScopes(v___x_2444_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_inc(v___x_2444_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1913_, v___x_2444_);
v___y_2650_ = v___x_2671_;
goto v___jp_2649_;
}
else
{
lean_object* v_view_2672_; lean_object* v_name_2673_; lean_object* v_imported_2674_; lean_object* v_ctx_2675_; lean_object* v_scopes_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2685_; 
lean_inc(v___x_2444_);
v_view_2672_ = l_Lean_extractMacroScopes(v___x_2444_);
v_name_2673_ = lean_ctor_get(v_view_2672_, 0);
v_imported_2674_ = lean_ctor_get(v_view_2672_, 1);
v_ctx_2675_ = lean_ctor_get(v_view_2672_, 2);
v_scopes_2676_ = lean_ctor_get(v_view_2672_, 3);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_view_2672_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2678_ = v_view_2672_;
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_scopes_2676_);
lean_inc(v_ctx_2675_);
lean_inc(v_imported_2674_);
lean_inc(v_name_2673_);
lean_dec(v_view_2672_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__0(v_structId_1913_, v_name_2673_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_imported_2674_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_ctx_2675_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_scopes_2676_);
v___x_2682_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_MacroScopesView_review(v___x_2682_);
v___y_2650_ = v___x_2683_;
goto v___jp_2649_;
}
}
}
v___jp_1942_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_ref_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_inc_ref(v___y_1966_);
v___x_1983_ = l_Array_append___redArg(v___y_1966_, v___y_1982_);
lean_dec_ref(v___y_1982_);
lean_inc_n(v___y_1948_, 4);
lean_inc_n(v___y_1977_, 18);
v___x_1984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1984_, 0, v___y_1977_);
lean_ctor_set(v___x_1984_, 1, v___y_1948_);
lean_ctor_set(v___x_1984_, 2, v___x_1983_);
lean_inc_n(v___y_1954_, 11);
lean_inc(v___y_1979_);
v___x_1985_ = l_Lean_Syntax_node7(v___y_1977_, v___y_1979_, v___y_1954_, v___y_1954_, v___x_1984_, v___y_1954_, v___y_1954_, v___y_1954_, v___y_1954_);
v___x_1986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_1971_, 3);
lean_inc_ref_n(v___y_1947_, 6);
lean_inc_ref_n(v___y_1975_, 6);
v___x_1987_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1971_, v___x_1986_);
v___x_1988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_1943_, 2);
v___x_1989_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1943_, v___x_1988_);
v___x_1990_ = l_Lean_Syntax_node1(v___y_1977_, v___x_1989_, v___y_1954_);
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1977_);
lean_ctor_set(v___x_1991_, 1, v___x_1986_);
v___x_1992_ = l_Lean_Syntax_node2(v___y_1977_, v___y_1974_, v___y_1955_, v___y_1954_);
v___x_1993_ = l_Lean_Syntax_node1(v___y_1977_, v___y_1948_, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_1995_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1971_, v___x_1994_);
lean_inc_ref(v___y_1968_);
v___x_1996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___y_1977_);
lean_ctor_set(v___x_1996_, 1, v___y_1968_);
v___x_1997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__5));
v___x_1998_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__6);
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__7));
lean_inc_n(v___y_1958_, 2);
lean_inc_n(v___y_1970_, 2);
v___x_2000_ = l_Lean_addMacroScope(v___y_1970_, v___x_1999_, v___y_1958_);
lean_inc_ref(v___y_1969_);
v___x_2001_ = l_Lean_Name_mkStr2(v___y_1969_, v___x_1997_);
lean_inc(v___y_1976_);
lean_inc(v___x_2001_);
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___y_1976_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_inc(v___y_1956_);
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___y_1956_);
v___x_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2002_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2006_, 0, v___y_1977_);
lean_ctor_set(v___x_2006_, 1, v___x_1998_);
lean_ctor_set(v___x_2006_, 2, v___x_2000_);
lean_ctor_set(v___x_2006_, 3, v___x_2005_);
lean_inc(v_type_1939_);
lean_inc(v___y_1960_);
lean_inc(v_structTy_1910_);
v___x_2007_ = l_Lean_Syntax_node3(v___y_1977_, v___y_1948_, v_structTy_1910_, v___y_1960_, v_type_1939_);
v___x_2008_ = l_Lean_Syntax_node2(v___y_1977_, v___y_1972_, v___x_2006_, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node2(v___y_1977_, v___y_1950_, v___x_1996_, v___x_2008_);
v___x_2010_ = l_Lean_Syntax_node2(v___y_1977_, v___x_1995_, v___y_1954_, v___x_2009_);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_2012_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1971_, v___x_2011_);
lean_inc_ref(v___y_1959_);
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___y_1977_);
lean_ctor_set(v___x_2013_, 1, v___y_1959_);
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2015_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1943_, v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_1977_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
lean_inc(v___y_1963_);
v___x_2018_ = l_Lean_Syntax_node1(v___y_1977_, v___y_1948_, v___y_1963_);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___y_1977_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_Syntax_node3(v___y_1977_, v___x_2015_, v___x_2017_, v___x_2018_, v___x_2020_);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2024_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___x_2022_, v___x_2023_);
v___x_2025_ = l_Lean_Syntax_node2(v___y_1977_, v___x_2024_, v___y_1954_, v___y_1954_);
v_ref_2026_ = l_Lean_replaceRef(v_fields_1932_, v___y_1973_);
lean_inc(v_ref_2026_);
lean_inc(v___y_1981_);
lean_inc(v___y_1952_);
lean_inc(v___y_1944_);
v___x_2027_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2027_, 0, v___y_1944_);
lean_ctor_set(v___x_2027_, 1, v___y_1970_);
lean_ctor_set(v___x_2027_, 2, v___y_1958_);
lean_ctor_set(v___x_2027_, 3, v___y_1952_);
lean_ctor_set(v___x_2027_, 4, v___y_1981_);
lean_ctor_set(v___x_2027_, 5, v_ref_2026_);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1930_, v_ref_2026_, v___x_2027_, v___y_1978_);
lean_dec_ref_known(v___x_2027_, 6);
lean_dec(v_ref_2026_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_n(v_a_2029_, 30);
v_a_2030_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2028_, 2);
lean_inc(v___y_1954_);
lean_inc_n(v___y_1977_, 2);
v___x_2031_ = l_Lean_Syntax_node4(v___y_1977_, v___x_2012_, v___x_2013_, v___x_2021_, v___x_2025_, v___y_1954_);
v___x_2032_ = l_Lean_Syntax_node6(v___y_1977_, v___x_1987_, v___x_1990_, v___x_1991_, v___y_1954_, v___x_1993_, v___x_2010_, v___x_2031_);
lean_inc(v___y_1962_);
v___x_2033_ = l_Lean_Syntax_node2(v___y_1977_, v___y_1962_, v___x_1985_, v___x_2032_);
v___x_2034_ = lean_array_push(v___y_1945_, v___x_2033_);
v___x_2035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref(v___y_1947_);
lean_inc_ref(v___y_1975_);
v___x_2036_ = l_Lean_Name_mkStr4(v___y_1975_, v___y_1947_, v___y_1943_, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_a_2029_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_1958_, 5);
lean_inc_n(v___y_1970_, 5);
v___x_2041_ = l_Lean_addMacroScope(v___y_1970_, v___x_2040_, v___y_1958_);
lean_inc_n(v___y_1956_, 5);
v___x_2042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2029_);
lean_ctor_set(v___x_2042_, 1, v___x_2039_);
lean_ctor_set(v___x_2042_, 2, v___x_2041_);
lean_ctor_set(v___x_2042_, 3, v___y_1956_);
lean_inc_ref(v___y_1966_);
lean_inc_n(v___y_1948_, 7);
v___x_2043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2043_, 0, v_a_2029_);
lean_ctor_set(v___x_2043_, 1, v___y_1948_);
lean_ctor_set(v___x_2043_, 2, v___y_1966_);
lean_inc_ref(v___y_1965_);
v___x_2044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_a_2029_);
lean_ctor_set(v___x_2044_, 1, v___y_1965_);
v___x_2045_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2047_ = l_Lean_addMacroScope(v___y_1970_, v___x_2046_, v___y_1958_);
v___x_2048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2048_, 0, v_a_2029_);
lean_ctor_set(v___x_2048_, 1, v___x_2045_);
lean_ctor_set(v___x_2048_, 2, v___x_2047_);
lean_ctor_set(v___x_2048_, 3, v___y_1956_);
lean_inc_ref_n(v___x_2043_, 17);
lean_inc_n(v___y_1961_, 2);
v___x_2049_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1961_, v___x_2048_, v___x_2043_);
lean_inc_ref(v___y_1959_);
v___x_2050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_a_2029_);
lean_ctor_set(v___x_2050_, 1, v___y_1959_);
lean_inc_ref_n(v___x_2050_, 2);
lean_inc_n(v___y_1980_, 2);
v___x_2051_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1980_, v___x_2050_, v___x_2043_, v___y_1960_);
v___x_2052_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1948_, v___x_2043_, v___x_2043_, v___x_2051_);
lean_inc_n(v___y_1946_, 2);
v___x_2053_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1946_, v___x_2049_, v___x_2052_);
v___x_2054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2056_ = l_Lean_addMacroScope(v___y_1970_, v___x_2055_, v___y_1958_);
v___x_2057_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2057_, 0, v_a_2029_);
lean_ctor_set(v___x_2057_, 1, v___x_2054_);
lean_ctor_set(v___x_2057_, 2, v___x_2056_);
lean_ctor_set(v___x_2057_, 3, v___y_1956_);
v___x_2058_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1961_, v___x_2057_, v___x_2043_);
lean_inc(v___y_1957_);
v___x_2059_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1980_, v___x_2050_, v___x_2043_, v___y_1957_);
v___x_2060_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1948_, v___x_2043_, v___x_2043_, v___x_2059_);
v___x_2061_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1946_, v___x_2058_, v___x_2060_);
v___x_2062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__36);
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__37));
v___x_2064_ = l_Lean_addMacroScope(v___y_1970_, v___x_2063_, v___y_1958_);
v___x_2065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2029_);
lean_ctor_set(v___x_2065_, 1, v___x_2062_);
lean_ctor_set(v___x_2065_, 2, v___x_2064_);
lean_ctor_set(v___x_2065_, 3, v___y_1956_);
v___x_2066_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1961_, v___x_2065_, v___x_2043_);
v___x_2067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__2);
v___x_2068_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1980_, v___x_2050_, v___x_2043_, v___x_2067_);
v___x_2069_ = l_Lean_Syntax_node3(v_a_2029_, v___y_1948_, v___x_2043_, v___x_2043_, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1946_, v___x_2066_, v___x_2069_);
v___x_2071_ = l_Lean_Syntax_node6(v_a_2029_, v___y_1948_, v___x_2053_, v___x_2043_, v___x_2061_, v___x_2043_, v___x_2070_, v___x_2043_);
v___x_2072_ = l_Lean_Syntax_node1(v_a_2029_, v___y_1949_, v___x_2071_);
v___x_2073_ = l_Lean_Syntax_node1(v_a_2029_, v___y_1953_, v___x_2043_);
lean_inc_ref(v___y_1968_);
v___x_2074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_a_2029_);
lean_ctor_set(v___x_2074_, 1, v___y_1968_);
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2078_ = l_Lean_addMacroScope(v___y_1970_, v___x_2077_, v___y_1958_);
lean_inc_ref(v___y_1969_);
v___x_2079_ = l_Lean_Name_mkStr2(v___y_1969_, v___x_2075_);
lean_inc(v___y_1976_);
lean_inc(v___x_2079_);
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___y_1976_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
v___x_2082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___y_1956_);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2084_, 0, v_a_2029_);
lean_ctor_set(v___x_2084_, 1, v___x_2076_);
lean_ctor_set(v___x_2084_, 2, v___x_2078_);
lean_ctor_set(v___x_2084_, 3, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_node2(v_a_2029_, v___y_1948_, v___x_2074_, v___x_2084_);
lean_inc_ref(v___y_1964_);
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_a_2029_);
lean_ctor_set(v___x_2086_, 1, v___y_1964_);
v___x_2087_ = l_Lean_Syntax_node6(v_a_2029_, v___y_1967_, v___x_2044_, v___x_2043_, v___x_2072_, v___x_2073_, v___x_2085_, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_node1(v_a_2029_, v___y_1948_, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_node5(v_a_2029_, v___x_2036_, v_fields_1932_, v___x_2038_, v___x_2042_, v___x_2043_, v___x_2088_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___x_2089_);
lean_ctor_set(v___x_1934_, 0, v___x_2034_);
v___x_2091_ = v___x_1934_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_nat_dec_lt(v___x_2092_, v___y_1951_);
if (v___x_2093_ == 0)
{
lean_dec(v___y_1963_);
lean_dec(v___y_1957_);
lean_dec(v___y_1951_);
v_a_1921_ = v___x_2091_;
v_a_1922_ = v_a_2030_;
goto v___jp_1920_;
}
else
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_nat_dec_le(v___y_1951_, v___y_1951_);
if (v___x_2094_ == 0)
{
if (v___x_2093_ == 0)
{
lean_dec(v___y_1963_);
lean_dec(v___y_1957_);
lean_dec(v___y_1951_);
v_a_1921_ = v___x_2091_;
v_a_1922_ = v_a_2030_;
goto v___jp_1920_;
}
else
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_of_nat(v___y_1951_);
lean_dec(v___y_1951_);
lean_inc(v_vis_x3f_1912_);
lean_inc(v_type_1939_);
lean_inc(v_structTy_1910_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1910_, v_type_1939_, v___y_1963_, v___y_1957_, v_vis_x3f_1912_, v_structId_1913_, v_ids_1938_, v___x_2095_, v___x_2096_, v___x_2091_, v___y_1918_, v_a_2030_);
v___y_1927_ = v___x_2097_;
goto v___jp_1926_;
}
}
else
{
size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_of_nat(v___y_1951_);
lean_dec(v___y_1951_);
lean_inc(v_vis_x3f_1912_);
lean_inc(v_type_1939_);
lean_inc(v_structTy_1910_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2(v_structTy_1910_, v_type_1939_, v___y_1963_, v___y_1957_, v_vis_x3f_1912_, v_structId_1913_, v_ids_1938_, v___x_2098_, v___x_2099_, v___x_2091_, v___y_1918_, v_a_2030_);
v___y_1927_ = v___x_2100_;
goto v___jp_1926_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v___x_2025_);
lean_dec(v___x_2021_);
lean_dec_ref_known(v___x_2013_, 2);
lean_dec(v___x_2012_);
lean_dec(v___x_2010_);
lean_dec(v___x_1993_);
lean_dec_ref_known(v___x_1991_, 2);
lean_dec(v___x_1990_);
lean_dec(v___x_1987_);
lean_dec(v___x_1985_);
lean_dec(v___y_1980_);
lean_dec(v___y_1977_);
lean_dec(v___y_1967_);
lean_dec(v___y_1963_);
lean_dec(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec(v___y_1957_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec(v___y_1951_);
lean_dec(v___y_1949_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1943_);
lean_del_object(v___x_1934_);
lean_dec(v_fields_1932_);
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v_a_2102_ = lean_ctor_get(v___x_2028_, 0);
v_a_2103_ = lean_ctor_get(v___x_2028_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2028_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_inc(v_a_2102_);
lean_dec(v___x_2028_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2102_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
v___jp_2111_:
{
lean_object* v___x_2150_; 
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1930_, v___y_2141_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_a_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_n(v_a_2151_, 2);
v_a_2152_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2150_, 2);
v___x_2153_ = l_Lean_mkIdentFrom(v___y_2112_, v___y_2149_, v___x_1930_);
lean_dec(v___y_2112_);
lean_inc_ref(v___y_2134_);
lean_inc(v___y_2118_);
v___x_2154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2151_);
lean_ctor_set(v___x_2154_, 1, v___y_2118_);
lean_ctor_set(v___x_2154_, 2, v___y_2134_);
if (lean_obj_tag(v_vis_x3f_1912_) == 1)
{
lean_object* v_val_2155_; lean_object* v___x_2156_; 
v_val_2155_ = lean_ctor_get(v_vis_x3f_1912_, 0);
lean_inc(v_val_2155_);
v___x_2156_ = l_Array_mkArray1___redArg(v_val_2155_);
v___y_1943_ = v___y_2114_;
v___y_1944_ = v___y_2113_;
v___y_1945_ = v___y_2115_;
v___y_1946_ = v___y_2116_;
v___y_1947_ = v___y_2117_;
v___y_1948_ = v___y_2118_;
v___y_1949_ = v___y_2119_;
v___y_1950_ = v___y_2120_;
v___y_1951_ = v___y_2121_;
v___y_1952_ = v___y_2122_;
v___y_1953_ = v___y_2123_;
v___y_1954_ = v___x_2154_;
v___y_1955_ = v___x_2153_;
v___y_1956_ = v___y_2124_;
v___y_1957_ = v___y_2125_;
v___y_1958_ = v___y_2126_;
v___y_1959_ = v___y_2127_;
v___y_1960_ = v___y_2128_;
v___y_1961_ = v___y_2129_;
v___y_1962_ = v___y_2130_;
v___y_1963_ = v___y_2131_;
v___y_1964_ = v___y_2132_;
v___y_1965_ = v___y_2133_;
v___y_1966_ = v___y_2134_;
v___y_1967_ = v___y_2136_;
v___y_1968_ = v___y_2135_;
v___y_1969_ = v___y_2137_;
v___y_1970_ = v___y_2138_;
v___y_1971_ = v___y_2140_;
v___y_1972_ = v___y_2139_;
v___y_1973_ = v___y_2141_;
v___y_1974_ = v___y_2144_;
v___y_1975_ = v___y_2143_;
v___y_1976_ = v___y_2142_;
v___y_1977_ = v_a_2151_;
v___y_1978_ = v_a_2152_;
v___y_1979_ = v___y_2145_;
v___y_1980_ = v___y_2146_;
v___y_1981_ = v___y_2148_;
v___y_1982_ = v___x_2156_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_mk_empty_array_with_capacity(v___y_2147_);
v___y_1943_ = v___y_2114_;
v___y_1944_ = v___y_2113_;
v___y_1945_ = v___y_2115_;
v___y_1946_ = v___y_2116_;
v___y_1947_ = v___y_2117_;
v___y_1948_ = v___y_2118_;
v___y_1949_ = v___y_2119_;
v___y_1950_ = v___y_2120_;
v___y_1951_ = v___y_2121_;
v___y_1952_ = v___y_2122_;
v___y_1953_ = v___y_2123_;
v___y_1954_ = v___x_2154_;
v___y_1955_ = v___x_2153_;
v___y_1956_ = v___y_2124_;
v___y_1957_ = v___y_2125_;
v___y_1958_ = v___y_2126_;
v___y_1959_ = v___y_2127_;
v___y_1960_ = v___y_2128_;
v___y_1961_ = v___y_2129_;
v___y_1962_ = v___y_2130_;
v___y_1963_ = v___y_2131_;
v___y_1964_ = v___y_2132_;
v___y_1965_ = v___y_2133_;
v___y_1966_ = v___y_2134_;
v___y_1967_ = v___y_2136_;
v___y_1968_ = v___y_2135_;
v___y_1969_ = v___y_2137_;
v___y_1970_ = v___y_2138_;
v___y_1971_ = v___y_2140_;
v___y_1972_ = v___y_2139_;
v___y_1973_ = v___y_2141_;
v___y_1974_ = v___y_2144_;
v___y_1975_ = v___y_2143_;
v___y_1976_ = v___y_2142_;
v___y_1977_ = v_a_2151_;
v___y_1978_ = v_a_2152_;
v___y_1979_ = v___y_2145_;
v___y_1980_ = v___y_2146_;
v___y_1981_ = v___y_2148_;
v___y_1982_ = v___x_2157_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_2158_; lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v___y_2149_);
lean_dec(v___y_2146_);
lean_dec(v___y_2144_);
lean_dec(v___y_2139_);
lean_dec(v___y_2136_);
lean_dec(v___y_2131_);
lean_dec(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec(v___y_2125_);
lean_dec(v___y_2123_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2112_);
lean_del_object(v___x_1934_);
lean_dec(v_fields_1932_);
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v_a_2158_ = lean_ctor_get(v___x_2150_, 0);
v_a_2159_ = lean_ctor_get(v___x_2150_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2150_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_inc(v_a_2158_);
lean_dec(v___x_2150_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2158_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
v___jp_2167_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_ref_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc_ref(v___y_2190_);
v___x_2206_ = l_Array_append___redArg(v___y_2190_, v___y_2205_);
lean_dec_ref(v___y_2205_);
lean_inc_n(v___y_2173_, 4);
lean_inc_n(v___y_2204_, 18);
v___x_2207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2204_);
lean_ctor_set(v___x_2207_, 1, v___y_2173_);
lean_ctor_set(v___x_2207_, 2, v___x_2206_);
lean_inc_n(v___y_2178_, 11);
lean_inc(v___y_2201_);
v___x_2208_ = l_Lean_Syntax_node7(v___y_2204_, v___y_2201_, v___y_2178_, v___y_2178_, v___x_2207_, v___y_2178_, v___y_2178_, v___y_2178_, v___y_2178_);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_2195_, 3);
lean_inc_ref_n(v___y_2172_, 6);
lean_inc_ref_n(v___y_2199_, 6);
v___x_2210_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2195_, v___x_2209_);
v___x_2211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__1));
lean_inc_ref_n(v___y_2168_, 2);
v___x_2212_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2168_, v___x_2211_);
v___x_2213_ = l_Lean_Syntax_node1(v___y_2204_, v___x_2212_, v___y_2178_);
v___x_2214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2204_);
lean_ctor_set(v___x_2214_, 1, v___x_2209_);
v___x_2215_ = l_Lean_Syntax_node2(v___y_2204_, v___y_2198_, v___y_2175_, v___y_2178_);
v___x_2216_ = l_Lean_Syntax_node1(v___y_2204_, v___y_2173_, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_2218_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2195_, v___x_2217_);
lean_inc_ref(v___y_2192_);
v___x_2219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2204_);
lean_ctor_set(v___x_2219_, 1, v___y_2192_);
v___x_2220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__3));
v___x_2221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__4);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__5));
lean_inc_n(v___y_2183_, 2);
lean_inc_n(v___y_2194_, 2);
v___x_2223_ = l_Lean_addMacroScope(v___y_2194_, v___x_2222_, v___y_2183_);
lean_inc_ref(v___y_2193_);
v___x_2224_ = l_Lean_Name_mkStr2(v___y_2193_, v___x_2220_);
lean_inc(v___y_2200_);
lean_inc(v___x_2224_);
v___x_2225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___y_2200_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_inc(v___y_2181_);
v___x_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___y_2181_);
v___x_2228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2204_);
lean_ctor_set(v___x_2229_, 1, v___x_2221_);
lean_ctor_set(v___x_2229_, 2, v___x_2223_);
lean_ctor_set(v___x_2229_, 3, v___x_2228_);
lean_inc(v_type_1939_);
lean_inc(v_structTy_1910_);
v___x_2230_ = l_Lean_Syntax_node2(v___y_2204_, v___y_2173_, v_structTy_1910_, v_type_1939_);
lean_inc(v___y_2196_);
v___x_2231_ = l_Lean_Syntax_node2(v___y_2204_, v___y_2196_, v___x_2229_, v___x_2230_);
v___x_2232_ = l_Lean_Syntax_node2(v___y_2204_, v___y_2176_, v___x_2219_, v___x_2231_);
v___x_2233_ = l_Lean_Syntax_node2(v___y_2204_, v___x_2218_, v___y_2178_, v___x_2232_);
v___x_2234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
v___x_2235_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2195_, v___x_2234_);
lean_inc_ref(v___y_2184_);
v___x_2236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___y_2204_);
lean_ctor_set(v___x_2236_, 1, v___y_2184_);
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__15));
v___x_2238_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2168_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_2240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2204_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_Syntax_node1(v___y_2204_, v___y_2173_, v___y_2187_);
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_2243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___y_2204_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node3(v___y_2204_, v___x_2238_, v___x_2240_, v___x_2241_, v___x_2243_);
v___x_2245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__18));
v___x_2246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__19));
v___x_2247_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___x_2245_, v___x_2246_);
v___x_2248_ = l_Lean_Syntax_node2(v___y_2204_, v___x_2247_, v___y_2178_, v___y_2178_);
v_ref_2249_ = l_Lean_replaceRef(v_fields_1932_, v___y_2197_);
lean_inc(v_ref_2249_);
lean_inc(v___y_2203_);
lean_inc(v___y_2179_);
lean_inc(v___y_2169_);
v___x_2250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2250_, 0, v___y_2169_);
lean_ctor_set(v___x_2250_, 1, v___y_2194_);
lean_ctor_set(v___x_2250_, 2, v___y_2183_);
lean_ctor_set(v___x_2250_, 3, v___y_2179_);
lean_ctor_set(v___x_2250_, 4, v___y_2203_);
lean_ctor_set(v___x_2250_, 5, v_ref_2249_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1930_, v_ref_2249_, v___x_2250_, v___y_2177_);
lean_dec_ref_known(v___x_2250_, 6);
lean_dec(v_ref_2249_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_ref_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_n(v_a_2252_, 14);
v_a_2253_ = lean_ctor_get(v___x_2251_, 1);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2251_, 2);
v___x_2254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__20));
lean_inc_ref_n(v___y_2168_, 2);
lean_inc_ref_n(v___y_2172_, 5);
lean_inc_ref_n(v___y_2199_, 7);
v___x_2255_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2168_, v___x_2254_);
v___x_2256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__21));
v___x_2257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_a_2252_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__7);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__8));
lean_inc_n(v___y_2183_, 4);
lean_inc_n(v___y_2194_, 4);
v___x_2260_ = l_Lean_addMacroScope(v___y_2194_, v___x_2259_, v___y_2183_);
lean_inc_n(v___y_2181_, 3);
v___x_2261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2252_);
lean_ctor_set(v___x_2261_, 1, v___x_2258_);
lean_ctor_set(v___x_2261_, 2, v___x_2260_);
lean_ctor_set(v___x_2261_, 3, v___y_2181_);
lean_inc_ref(v___y_2190_);
lean_inc_n(v___y_2173_, 3);
v___x_2262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2262_, 0, v_a_2252_);
lean_ctor_set(v___x_2262_, 1, v___y_2173_);
lean_ctor_set(v___x_2262_, 2, v___y_2190_);
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__9));
v___x_2264_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2168_, v___x_2263_);
v___x_2265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__10));
v___x_2266_ = l_Lean_Name_mkStr4(v___y_2199_, v___y_2172_, v___y_2168_, v___x_2265_);
v___x_2267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__11));
v___x_2268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_a_2252_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__13));
v___x_2270_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__15);
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Lean_addMacroScope(v___y_2194_, v___x_2271_, v___y_2183_);
lean_inc_ref_n(v___y_2193_, 2);
v___x_2273_ = l_Lean_Name_mkStr1(v___y_2193_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_inc_ref(v___y_2195_);
v___x_2275_ = l_Lean_Name_mkStr3(v___y_2199_, v___y_2172_, v___y_2195_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___x_2277_ = l_Lean_Name_mkStr2(v___y_2199_, v___y_2172_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__16));
v___x_2280_ = l_Lean_Name_mkStr2(v___y_2199_, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
v___x_2282_ = l_Lean_Name_mkStr1(v___y_2199_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v___y_2181_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2281_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2278_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2276_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2274_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2289_, 0, v_a_2252_);
lean_ctor_set(v___x_2289_, 1, v___x_2270_);
lean_ctor_set(v___x_2289_, 2, v___x_2272_);
lean_ctor_set(v___x_2289_, 3, v___x_2288_);
v___x_2290_ = l_Lean_Syntax_node1(v_a_2252_, v___x_2269_, v___x_2289_);
v___x_2291_ = l_Lean_Syntax_node2(v_a_2252_, v___x_2266_, v___x_2268_, v___x_2290_);
v___x_2292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__18);
v___x_2293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__21));
v___x_2296_ = l_Lean_addMacroScope(v___y_2194_, v___x_2295_, v___y_2183_);
v___x_2297_ = l_Lean_Name_mkStr3(v___y_2193_, v___x_2293_, v___x_2294_);
lean_inc(v___y_2200_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___y_2200_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___y_2181_);
v___x_2300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2300_, 0, v_a_2252_);
lean_ctor_set(v___x_2300_, 1, v___x_2292_);
lean_ctor_set(v___x_2300_, 2, v___x_2296_);
lean_ctor_set(v___x_2300_, 3, v___x_2299_);
lean_inc(v_type_1939_);
v___x_2301_ = l_Lean_Syntax_node1(v_a_2252_, v___y_2173_, v_type_1939_);
v___x_2302_ = l_Lean_Syntax_node2(v_a_2252_, v___y_2196_, v___x_2300_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__22));
v___x_2304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2252_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_Syntax_node3(v_a_2252_, v___x_2264_, v___x_2291_, v___x_2302_, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_node1(v_a_2252_, v___y_2173_, v___x_2305_);
lean_inc(v___x_2255_);
v___x_2307_ = l_Lean_Syntax_node5(v_a_2252_, v___x_2255_, v_fields_1932_, v___x_2257_, v___x_2261_, v___x_2262_, v___x_2306_);
v_ref_2308_ = l_Lean_replaceRef(v___x_2307_, v___y_2197_);
lean_inc(v_ref_2308_);
lean_inc(v___y_2203_);
lean_inc(v___y_2179_);
lean_inc(v___y_2169_);
v___x_2309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2309_, 0, v___y_2169_);
lean_ctor_set(v___x_2309_, 1, v___y_2194_);
lean_ctor_set(v___x_2309_, 2, v___y_2183_);
lean_ctor_set(v___x_2309_, 3, v___y_2179_);
lean_ctor_set(v___x_2309_, 4, v___y_2203_);
lean_ctor_set(v___x_2309_, 5, v_ref_2308_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1930_, v_ref_2308_, v___x_2309_, v_a_2253_);
lean_dec_ref_known(v___x_2309_, 6);
lean_dec(v_ref_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_n(v_a_2311_, 29);
v_a_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 2);
lean_inc(v___y_2178_);
lean_inc_n(v___y_2204_, 2);
v___x_2313_ = l_Lean_Syntax_node4(v___y_2204_, v___x_2235_, v___x_2236_, v___x_2244_, v___x_2248_, v___y_2178_);
v___x_2314_ = l_Lean_Syntax_node6(v___y_2204_, v___x_2210_, v___x_2213_, v___x_2214_, v___y_2178_, v___x_2216_, v___x_2233_, v___x_2313_);
lean_inc(v___y_2186_);
v___x_2315_ = l_Lean_Syntax_node2(v___y_2204_, v___y_2186_, v___x_2208_, v___x_2314_);
v___x_2316_ = lean_array_push(v___y_2170_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_a_2311_);
lean_ctor_set(v___x_2317_, 1, v___x_2256_);
v___x_2318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__23);
v___x_2319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__24));
lean_inc_n(v___y_2183_, 6);
lean_inc_n(v___y_2194_, 6);
v___x_2320_ = l_Lean_addMacroScope(v___y_2194_, v___x_2319_, v___y_2183_);
lean_inc_n(v___y_2181_, 6);
v___x_2321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2311_);
lean_ctor_set(v___x_2321_, 1, v___x_2318_);
lean_ctor_set(v___x_2321_, 2, v___x_2320_);
lean_ctor_set(v___x_2321_, 3, v___y_2181_);
lean_inc_ref(v___y_2190_);
lean_inc_n(v___y_2173_, 6);
v___x_2322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2311_);
lean_ctor_set(v___x_2322_, 1, v___y_2173_);
lean_ctor_set(v___x_2322_, 2, v___y_2190_);
lean_inc_ref(v___y_2189_);
v___x_2323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2311_);
lean_ctor_set(v___x_2323_, 1, v___y_2189_);
v___x_2324_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__29);
v___x_2325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__30));
v___x_2326_ = l_Lean_addMacroScope(v___y_2194_, v___x_2325_, v___y_2183_);
v___x_2327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2311_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
lean_ctor_set(v___x_2327_, 2, v___x_2326_);
lean_ctor_set(v___x_2327_, 3, v___y_2181_);
lean_inc_ref_n(v___x_2322_, 14);
lean_inc_n(v___y_2185_, 2);
v___x_2328_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2185_, v___x_2327_, v___x_2322_);
lean_inc_ref(v___y_2184_);
v___x_2329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2311_);
lean_ctor_set(v___x_2329_, 1, v___y_2184_);
lean_inc_ref(v___x_2329_);
lean_inc(v___y_2202_);
v___x_2330_ = l_Lean_Syntax_node3(v_a_2311_, v___y_2202_, v___x_2329_, v___x_2322_, v___y_2182_);
v___x_2331_ = l_Lean_Syntax_node3(v_a_2311_, v___y_2173_, v___x_2322_, v___x_2322_, v___x_2330_);
lean_inc(v___x_2331_);
lean_inc_n(v___y_2171_, 2);
v___x_2332_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2171_, v___x_2328_, v___x_2331_);
v___x_2333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__33);
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__34));
v___x_2335_ = l_Lean_addMacroScope(v___y_2194_, v___x_2334_, v___y_2183_);
v___x_2336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2311_);
lean_ctor_set(v___x_2336_, 1, v___x_2333_);
lean_ctor_set(v___x_2336_, 2, v___x_2335_);
lean_ctor_set(v___x_2336_, 3, v___y_2181_);
v___x_2337_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2185_, v___x_2336_, v___x_2322_);
v___x_2338_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2171_, v___x_2337_, v___x_2331_);
v___x_2339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__24);
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__25));
v___x_2341_ = l_Lean_addMacroScope(v___y_2194_, v___x_2340_, v___y_2183_);
v___x_2342_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2342_, 0, v_a_2311_);
lean_ctor_set(v___x_2342_, 1, v___x_2339_);
lean_ctor_set(v___x_2342_, 2, v___x_2341_);
lean_ctor_set(v___x_2342_, 3, v___y_2181_);
v___x_2343_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2185_, v___x_2342_, v___x_2322_);
v___x_2344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__26);
v___x_2345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__27));
v___x_2346_ = l_Lean_addMacroScope(v___y_2194_, v___x_2345_, v___y_2183_);
v___x_2347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__1));
lean_inc_n(v___y_2200_, 2);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___y_2200_);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___y_2181_);
v___x_2350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2311_);
lean_ctor_set(v___x_2350_, 1, v___x_2344_);
lean_ctor_set(v___x_2350_, 2, v___x_2346_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
v___x_2351_ = l_Lean_Syntax_node3(v_a_2311_, v___y_2202_, v___x_2329_, v___x_2322_, v___x_2350_);
v___x_2352_ = l_Lean_Syntax_node3(v_a_2311_, v___y_2173_, v___x_2322_, v___x_2322_, v___x_2351_);
v___x_2353_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2171_, v___x_2343_, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node6(v_a_2311_, v___y_2173_, v___x_2332_, v___x_2322_, v___x_2338_, v___x_2322_, v___x_2353_, v___x_2322_);
v___x_2355_ = l_Lean_Syntax_node1(v_a_2311_, v___y_2174_, v___x_2354_);
v___x_2356_ = l_Lean_Syntax_node1(v_a_2311_, v___y_2180_, v___x_2322_);
lean_inc_ref(v___y_2192_);
v___x_2357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_a_2311_);
lean_ctor_set(v___x_2357_, 1, v___y_2192_);
v___x_2358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__43));
v___x_2359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__44);
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__45));
v___x_2361_ = l_Lean_addMacroScope(v___y_2194_, v___x_2360_, v___y_2183_);
lean_inc_ref(v___y_2193_);
v___x_2362_ = l_Lean_Name_mkStr2(v___y_2193_, v___x_2358_);
lean_inc(v___x_2362_);
v___x_2363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___y_2200_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
v___x_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
lean_ctor_set(v___x_2365_, 1, v___y_2181_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2311_);
lean_ctor_set(v___x_2367_, 1, v___x_2359_);
lean_ctor_set(v___x_2367_, 2, v___x_2361_);
lean_ctor_set(v___x_2367_, 3, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node2(v_a_2311_, v___y_2173_, v___x_2357_, v___x_2367_);
lean_inc_ref(v___y_2188_);
v___x_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2311_);
lean_ctor_set(v___x_2369_, 1, v___y_2188_);
v___x_2370_ = l_Lean_Syntax_node6(v_a_2311_, v___y_2191_, v___x_2323_, v___x_2322_, v___x_2355_, v___x_2356_, v___x_2368_, v___x_2369_);
v___x_2371_ = l_Lean_Syntax_node1(v_a_2311_, v___y_2173_, v___x_2370_);
v___x_2372_ = l_Lean_Syntax_node5(v_a_2311_, v___x_2255_, v___x_2307_, v___x_2317_, v___x_2321_, v___x_2322_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2316_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v_a_1921_ = v___x_2373_;
v_a_1922_ = v_a_2312_;
goto v___jp_1920_;
}
else
{
lean_object* v_a_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v___x_2307_);
lean_dec(v___x_2255_);
lean_dec(v___x_2248_);
lean_dec(v___x_2244_);
lean_dec_ref_known(v___x_2236_, 2);
lean_dec(v___x_2235_);
lean_dec(v___x_2233_);
lean_dec(v___x_2216_);
lean_dec_ref_known(v___x_2214_, 2);
lean_dec(v___x_2213_);
lean_dec(v___x_2210_);
lean_dec(v___x_2208_);
lean_dec(v___y_2204_);
lean_dec(v___y_2202_);
lean_dec(v___y_2191_);
lean_dec(v___y_2185_);
lean_dec(v___y_2182_);
lean_dec(v___y_2180_);
lean_dec(v___y_2178_);
lean_dec(v___y_2174_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v_a_2374_ = lean_ctor_get(v___x_2310_, 0);
v_a_2375_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2310_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_inc(v_a_2374_);
lean_dec(v___x_2310_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2374_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v___x_2248_);
lean_dec(v___x_2244_);
lean_dec_ref_known(v___x_2236_, 2);
lean_dec(v___x_2235_);
lean_dec(v___x_2233_);
lean_dec(v___x_2216_);
lean_dec_ref_known(v___x_2214_, 2);
lean_dec(v___x_2213_);
lean_dec(v___x_2210_);
lean_dec(v___x_2208_);
lean_dec(v___y_2204_);
lean_dec(v___y_2202_);
lean_dec(v___y_2196_);
lean_dec(v___y_2191_);
lean_dec(v___y_2185_);
lean_dec(v___y_2182_);
lean_dec(v___y_2180_);
lean_dec(v___y_2178_);
lean_dec(v___y_2174_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec_ref(v___y_2168_);
lean_dec(v_fields_1932_);
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v_a_2383_ = lean_ctor_get(v___x_2251_, 0);
v_a_2384_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2251_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_inc(v_a_2383_);
lean_dec(v___x_2251_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2383_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
v___jp_2392_:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__1(v___x_1930_, v___y_2419_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v_a_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc_n(v_a_2428_, 2);
v_a_2429_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2427_, 2);
v___x_2430_ = l_Lean_mkIdentFrom(v_id_1937_, v___y_2426_, v___x_1930_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2398_);
v___x_2431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2428_);
lean_ctor_set(v___x_2431_, 1, v___y_2398_);
lean_ctor_set(v___x_2431_, 2, v___y_2412_);
if (lean_obj_tag(v_vis_x3f_1912_) == 1)
{
lean_object* v_val_2432_; lean_object* v___x_2433_; 
v_val_2432_ = lean_ctor_get(v_vis_x3f_1912_, 0);
lean_inc(v_val_2432_);
v___x_2433_ = l_Array_mkArray1___redArg(v_val_2432_);
v___y_2168_ = v___y_2394_;
v___y_2169_ = v___y_2393_;
v___y_2170_ = v___y_2395_;
v___y_2171_ = v___y_2396_;
v___y_2172_ = v___y_2397_;
v___y_2173_ = v___y_2398_;
v___y_2174_ = v___y_2399_;
v___y_2175_ = v___x_2430_;
v___y_2176_ = v___y_2400_;
v___y_2177_ = v_a_2429_;
v___y_2178_ = v___x_2431_;
v___y_2179_ = v___y_2401_;
v___y_2180_ = v___y_2402_;
v___y_2181_ = v___y_2403_;
v___y_2182_ = v___y_2404_;
v___y_2183_ = v___y_2405_;
v___y_2184_ = v___y_2406_;
v___y_2185_ = v___y_2407_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v___y_2409_;
v___y_2188_ = v___y_2410_;
v___y_2189_ = v___y_2411_;
v___y_2190_ = v___y_2412_;
v___y_2191_ = v___y_2413_;
v___y_2192_ = v___y_2414_;
v___y_2193_ = v___y_2415_;
v___y_2194_ = v___y_2416_;
v___y_2195_ = v___y_2418_;
v___y_2196_ = v___y_2417_;
v___y_2197_ = v___y_2419_;
v___y_2198_ = v___y_2422_;
v___y_2199_ = v___y_2421_;
v___y_2200_ = v___y_2420_;
v___y_2201_ = v___y_2423_;
v___y_2202_ = v___y_2424_;
v___y_2203_ = v___y_2425_;
v___y_2204_ = v_a_2428_;
v___y_2205_ = v___x_2433_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2434_; 
v___x_2434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2168_ = v___y_2394_;
v___y_2169_ = v___y_2393_;
v___y_2170_ = v___y_2395_;
v___y_2171_ = v___y_2396_;
v___y_2172_ = v___y_2397_;
v___y_2173_ = v___y_2398_;
v___y_2174_ = v___y_2399_;
v___y_2175_ = v___x_2430_;
v___y_2176_ = v___y_2400_;
v___y_2177_ = v_a_2429_;
v___y_2178_ = v___x_2431_;
v___y_2179_ = v___y_2401_;
v___y_2180_ = v___y_2402_;
v___y_2181_ = v___y_2403_;
v___y_2182_ = v___y_2404_;
v___y_2183_ = v___y_2405_;
v___y_2184_ = v___y_2406_;
v___y_2185_ = v___y_2407_;
v___y_2186_ = v___y_2408_;
v___y_2187_ = v___y_2409_;
v___y_2188_ = v___y_2410_;
v___y_2189_ = v___y_2411_;
v___y_2190_ = v___y_2412_;
v___y_2191_ = v___y_2413_;
v___y_2192_ = v___y_2414_;
v___y_2193_ = v___y_2415_;
v___y_2194_ = v___y_2416_;
v___y_2195_ = v___y_2418_;
v___y_2196_ = v___y_2417_;
v___y_2197_ = v___y_2419_;
v___y_2198_ = v___y_2422_;
v___y_2199_ = v___y_2421_;
v___y_2200_ = v___y_2420_;
v___y_2201_ = v___y_2423_;
v___y_2202_ = v___y_2424_;
v___y_2203_ = v___y_2425_;
v___y_2204_ = v_a_2428_;
v___y_2205_ = v___x_2434_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___y_2426_);
lean_dec(v___y_2424_);
lean_dec(v___y_2422_);
lean_dec(v___y_2417_);
lean_dec(v___y_2413_);
lean_dec(v___y_2409_);
lean_dec(v___y_2407_);
lean_dec(v___y_2404_);
lean_dec(v___y_2402_);
lean_dec(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v_fields_1932_);
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v_a_2435_ = lean_ctor_get(v___x_2427_, 0);
v_a_2436_ = lean_ctor_get(v___x_2427_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_inc(v_a_2435_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
v___jp_2445_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_inc_ref_n(v___y_2449_, 2);
v___x_2463_ = l_Array_append___redArg(v___y_2449_, v___y_2462_);
lean_dec_ref(v___y_2462_);
lean_inc_n(v___y_2451_, 19);
lean_inc_n(v___y_2452_, 69);
v___x_2464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2464_, 0, v___y_2452_);
lean_ctor_set(v___x_2464_, 1, v___y_2451_);
lean_ctor_set(v___x_2464_, 2, v___x_2463_);
lean_inc_n(v___y_2456_, 35);
lean_inc(v___y_2459_);
v___x_2465_ = l_Lean_Syntax_node7(v___y_2452_, v___y_2459_, v___y_2456_, v___y_2456_, v___x_2464_, v___y_2456_, v___y_2456_, v___y_2456_, v___y_2456_);
v___x_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_2454_, 4);
lean_inc_ref_n(v___y_2450_, 15);
lean_inc_ref_n(v___y_2457_, 15);
v___x_2467_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___y_2454_, v___x_2466_);
v___x_2468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_2469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___y_2452_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_2471_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___y_2454_, v___x_2470_);
lean_inc(v___y_2447_);
lean_inc(v___x_2471_);
v___x_2472_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2471_, v___y_2447_, v___y_2456_);
v___x_2473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_2474_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___y_2454_, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_2476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__2));
v___x_2477_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_2479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2452_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__4));
v___x_2481_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2480_);
v___x_2482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__32);
v___x_2483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__33));
lean_inc_n(v___y_2461_, 8);
lean_inc_n(v___y_2453_, 8);
v___x_2484_ = l_Lean_addMacroScope(v___y_2453_, v___x_2483_, v___y_2461_);
v___x_2485_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_2486_ = lean_box(0);
v___x_2487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__38));
v___x_2488_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2488_, 0, v___y_2452_);
lean_ctor_set(v___x_2488_, 1, v___x_2482_);
lean_ctor_set(v___x_2488_, 2, v___x_2484_);
lean_ctor_set(v___x_2488_, 3, v___x_2487_);
lean_inc(v_type_1939_);
lean_inc(v_structTy_1910_);
v___x_2489_ = l_Lean_Syntax_node2(v___y_2452_, v___y_2451_, v_structTy_1910_, v_type_1939_);
lean_inc_n(v___x_2481_, 2);
v___x_2490_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2481_, v___x_2488_, v___x_2489_);
lean_inc(v___x_2477_);
v___x_2491_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2477_, v___x_2479_, v___x_2490_);
v___x_2492_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_2491_);
v___x_2493_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2474_, v___y_2456_, v___x_2492_);
v___x_2494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__39));
v___x_2495_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___y_2454_, v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___y_2452_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__27));
v___x_2499_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2498_);
v___x_2500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__0));
v___x_2501_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2500_);
v___x_2502_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__1));
v___x_2503_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2502_);
v___x_2504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__42);
v___x_2505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__43));
v___x_2506_ = l_Lean_addMacroScope(v___y_2453_, v___x_2505_, v___y_2461_);
v___x_2507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__47));
v___x_2508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2452_);
lean_ctor_set(v___x_2508_, 1, v___x_2504_);
lean_ctor_set(v___x_2508_, 2, v___x_2506_);
lean_ctor_set(v___x_2508_, 3, v___x_2507_);
lean_inc_n(v___x_2503_, 5);
v___x_2509_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2503_, v___x_2508_, v___y_2456_);
v___x_2510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__49);
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__50));
v___x_2512_ = l_Lean_addMacroScope(v___y_2453_, v___x_2511_, v___y_2461_);
v___x_2513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2452_);
lean_ctor_set(v___x_2513_, 1, v___x_2510_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
lean_ctor_set(v___x_2513_, 3, v___x_2486_);
lean_inc_ref_n(v___x_2513_, 3);
v___x_2514_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_2513_);
v___x_2515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__31));
v___x_2516_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2452_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__51));
v___x_2520_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__52));
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2452_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
lean_inc_n(v_id_1937_, 3);
v___x_2523_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2520_, v___x_2513_, v___x_2522_, v_id_1937_);
lean_inc(v___x_2523_);
lean_inc_ref_n(v___x_2518_, 5);
lean_inc_n(v___x_2516_, 6);
v___x_2524_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2523_);
lean_inc(v___x_2514_);
v___x_2525_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___x_2514_, v___y_2456_, v___x_2524_);
lean_inc_n(v___x_2501_, 6);
v___x_2526_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2509_, v___x_2525_);
v___x_2527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__54);
v___x_2528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__55));
v___x_2529_ = l_Lean_addMacroScope(v___y_2453_, v___x_2528_, v___y_2461_);
v___x_2530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__59));
v___x_2531_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2531_, 0, v___y_2452_);
lean_ctor_set(v___x_2531_, 1, v___x_2527_);
lean_ctor_set(v___x_2531_, 2, v___x_2529_);
lean_ctor_set(v___x_2531_, 3, v___x_2530_);
v___x_2532_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2503_, v___x_2531_, v___y_2456_);
v___x_2533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__61);
v___x_2534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__62));
v___x_2535_ = l_Lean_addMacroScope(v___y_2453_, v___x_2534_, v___y_2461_);
v___x_2536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2452_);
lean_ctor_set(v___x_2536_, 1, v___x_2533_);
lean_ctor_set(v___x_2536_, 2, v___x_2535_);
lean_ctor_set(v___x_2536_, 3, v___x_2486_);
lean_inc_ref(v___x_2536_);
v___x_2537_ = l_Lean_Syntax_node2(v___y_2452_, v___y_2451_, v___x_2536_, v___x_2513_);
v___x_2538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__25));
v___x_2539_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2538_);
v___x_2540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___y_2452_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__63));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___y_2452_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Lean_Syntax_node2(v___y_2452_, v___y_2451_, v___x_2514_, v___x_2543_);
v___x_2545_ = lean_box(0);
v___x_2546_ = l_Lean_SourceInfo_fromRef(v___x_2545_, v___x_1930_);
lean_inc(v___x_2546_);
v___x_2547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___y_2451_);
lean_ctor_set(v___x_2547_, 2, v___y_2449_);
v___x_2548_ = l_Lean_Syntax_node2(v___x_2546_, v___x_2503_, v_id_1937_, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2536_);
v___x_2550_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___y_2456_, v___y_2456_, v___x_2549_);
lean_inc(v___x_2548_);
v___x_2551_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2548_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_2551_);
lean_inc_n(v___x_2499_, 3);
v___x_2553_ = l_Lean_Syntax_node1(v___y_2452_, v___x_2499_, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__42));
v___x_2555_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2554_);
lean_inc(v___x_2555_);
v___x_2556_ = l_Lean_Syntax_node1(v___y_2452_, v___x_2555_, v___y_2456_);
v___x_2557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2452_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
lean_inc_ref(v___x_2558_);
lean_inc(v___x_2556_);
lean_inc(v___x_2544_);
lean_inc_ref(v___x_2541_);
lean_inc_n(v___x_2539_, 2);
v___x_2559_ = l_Lean_Syntax_node6(v___y_2452_, v___x_2539_, v___x_2541_, v___x_2544_, v___x_2553_, v___x_2556_, v___y_2456_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___x_2537_, v___y_2456_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2532_, v___x_2561_);
v___x_2563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__65);
v___x_2564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__66));
v___x_2565_ = l_Lean_addMacroScope(v___y_2453_, v___x_2564_, v___y_2461_);
v___x_2566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__68));
v___x_2567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2567_, 0, v___y_2452_);
lean_ctor_set(v___x_2567_, 1, v___x_2563_);
lean_ctor_set(v___x_2567_, 2, v___x_2565_);
lean_ctor_set(v___x_2567_, 3, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2503_, v___x_2567_, v___y_2456_);
v___x_2569_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__70);
v___x_2570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__71));
v___x_2571_ = l_Lean_addMacroScope(v___y_2453_, v___x_2570_, v___y_2461_);
v___x_2572_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2572_, 0, v___y_2452_);
lean_ctor_set(v___x_2572_, 1, v___x_2569_);
lean_ctor_set(v___x_2572_, 2, v___x_2571_);
lean_ctor_set(v___x_2572_, 3, v___x_2486_);
lean_inc_ref(v___x_2572_);
v___x_2573_ = l_Lean_Syntax_node2(v___y_2452_, v___y_2451_, v___x_2572_, v___x_2513_);
v___x_2574_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_2523_);
v___x_2575_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2481_, v___x_2572_, v___x_2574_);
v___x_2576_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2575_);
v___x_2577_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___y_2456_, v___y_2456_, v___x_2576_);
v___x_2578_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2548_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_2578_);
v___x_2580_ = l_Lean_Syntax_node1(v___y_2452_, v___x_2499_, v___x_2579_);
v___x_2581_ = l_Lean_Syntax_node6(v___y_2452_, v___x_2539_, v___x_2541_, v___x_2544_, v___x_2580_, v___x_2556_, v___y_2456_, v___x_2558_);
v___x_2582_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___x_2573_, v___y_2456_, v___x_2582_);
v___x_2584_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2568_, v___x_2583_);
v___x_2585_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__73);
v___x_2586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__74));
v___x_2587_ = l_Lean_addMacroScope(v___y_2453_, v___x_2586_, v___y_2461_);
v___x_2588_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2588_, 0, v___y_2452_);
lean_ctor_set(v___x_2588_, 1, v___x_2585_);
lean_ctor_set(v___x_2588_, 2, v___x_2587_);
lean_ctor_set(v___x_2588_, 3, v___x_2486_);
v___x_2589_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2503_, v___x_2588_, v___y_2456_);
v___x_2590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
v___x_2591_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2452_);
lean_ctor_set(v___x_2592_, 1, v___x_2590_);
v___x_2593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_2594_ = l_Lean_Name_mkStr4(v___y_2457_, v___y_2450_, v___x_2475_, v___x_2593_);
lean_inc(v___x_1911_);
v___x_2595_ = l_Lean_Syntax_node1(v___y_2452_, v___y_2451_, v___x_1911_);
v___x_2596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_2597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___y_2452_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
lean_inc(v_defVal_1940_);
v___x_2598_ = l_Lean_Syntax_node4(v___y_2452_, v___x_2594_, v___x_2595_, v___y_2456_, v___x_2597_, v_defVal_1940_);
v___x_2599_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2591_, v___x_2592_, v___x_2598_);
v___x_2600_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2516_, v___x_2518_, v___y_2456_, v___x_2599_);
v___x_2601_ = l_Lean_Syntax_node3(v___y_2452_, v___y_2451_, v___y_2456_, v___y_2456_, v___x_2600_);
v___x_2602_ = l_Lean_Syntax_node2(v___y_2452_, v___x_2501_, v___x_2589_, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node7(v___y_2452_, v___y_2451_, v___x_2526_, v___y_2456_, v___x_2562_, v___y_2456_, v___x_2584_, v___y_2456_, v___x_2602_);
v___x_2604_ = l_Lean_Syntax_node1(v___y_2452_, v___x_2499_, v___x_2603_);
v___x_2605_ = l_Lean_Syntax_node3(v___y_2452_, v___x_2495_, v___x_2497_, v___x_2604_, v___y_2456_);
v___x_2606_ = l_Lean_Syntax_node5(v___y_2452_, v___x_2467_, v___x_2469_, v___x_2472_, v___x_2493_, v___x_2605_, v___y_2456_);
lean_inc(v___y_2446_);
v___x_2607_ = l_Lean_Syntax_node2(v___y_2452_, v___y_2446_, v___x_2465_, v___x_2606_);
v___x_2608_ = lean_array_push(v_cmds_1931_, v___x_2607_);
lean_inc(v___x_2444_);
v___x_2609_ = l_Lake_Name_quoteFrom(v_id_1937_, v___x_2444_, v___x_1930_);
if (v_parent_1941_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
lean_dec(v___x_2444_);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_array_get_size(v_ids_1938_);
v___x_2612_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec(v___x_2609_);
lean_dec(v___x_2555_);
lean_dec(v___x_2539_);
lean_dec(v___x_2516_);
lean_dec(v___x_2503_);
lean_dec(v___x_2501_);
lean_dec(v___x_2499_);
lean_dec(v___x_2481_);
lean_dec(v___x_2477_);
lean_dec(v___x_2471_);
lean_dec(v___y_2447_);
lean_del_object(v___x_1934_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2608_);
lean_ctor_set(v___x_2613_, 1, v_fields_1932_);
v_a_1921_ = v___x_2613_;
v_a_1922_ = v___y_1919_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2614_ = lean_array_fget_borrowed(v_ids_1938_, v___x_2610_);
v___x_2615_ = l_Lean_TSyntax_getId(v___x_2614_);
lean_inc(v___x_2615_);
lean_inc(v___x_2614_);
v___x_2616_ = l_Lake_Name_quoteFrom(v___x_2614_, v___x_2615_, v___x_1930_);
v___x_2617_ = l_Lean_Name_hasMacroScopes(v___x_2615_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1913_, v___x_2615_);
lean_inc(v___x_2614_);
v___y_2112_ = v___x_2614_;
v___y_2113_ = v___y_2448_;
v___y_2114_ = v___x_2475_;
v___y_2115_ = v___x_2608_;
v___y_2116_ = v___x_2501_;
v___y_2117_ = v___y_2450_;
v___y_2118_ = v___y_2451_;
v___y_2119_ = v___x_2499_;
v___y_2120_ = v___x_2477_;
v___y_2121_ = v___x_2611_;
v___y_2122_ = v___y_2458_;
v___y_2123_ = v___x_2555_;
v___y_2124_ = v___x_2486_;
v___y_2125_ = v___x_2609_;
v___y_2126_ = v___y_2461_;
v___y_2127_ = v___x_2517_;
v___y_2128_ = v___x_2616_;
v___y_2129_ = v___x_2503_;
v___y_2130_ = v___y_2446_;
v___y_2131_ = v___y_2447_;
v___y_2132_ = v___x_2557_;
v___y_2133_ = v___x_2540_;
v___y_2134_ = v___y_2449_;
v___y_2135_ = v___x_2478_;
v___y_2136_ = v___x_2539_;
v___y_2137_ = v___x_2485_;
v___y_2138_ = v___y_2453_;
v___y_2139_ = v___x_2481_;
v___y_2140_ = v___y_2454_;
v___y_2141_ = v___y_2455_;
v___y_2142_ = v___x_2486_;
v___y_2143_ = v___y_2457_;
v___y_2144_ = v___x_2471_;
v___y_2145_ = v___y_2459_;
v___y_2146_ = v___x_2516_;
v___y_2147_ = v___x_2610_;
v___y_2148_ = v___y_2460_;
v___y_2149_ = v___x_2618_;
goto v___jp_2111_;
}
else
{
lean_object* v_view_2619_; lean_object* v_name_2620_; lean_object* v_imported_2621_; lean_object* v_ctx_2622_; lean_object* v_scopes_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
v_view_2619_ = l_Lean_extractMacroScopes(v___x_2615_);
v_name_2620_ = lean_ctor_get(v_view_2619_, 0);
v_imported_2621_ = lean_ctor_get(v_view_2619_, 1);
v_ctx_2622_ = lean_ctor_get(v_view_2619_, 2);
v_scopes_2623_ = lean_ctor_get(v_view_2619_, 3);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_view_2619_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2625_ = v_view_2619_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_scopes_2623_);
lean_inc(v_ctx_2622_);
lean_inc(v_imported_2621_);
lean_inc(v_name_2620_);
lean_dec(v_view_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2___lam__0(v_structId_1913_, v_name_2620_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_imported_2621_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_ctx_2622_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_scopes_2623_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_MacroScopesView_review(v___x_2629_);
lean_inc(v___x_2614_);
v___y_2112_ = v___x_2614_;
v___y_2113_ = v___y_2448_;
v___y_2114_ = v___x_2475_;
v___y_2115_ = v___x_2608_;
v___y_2116_ = v___x_2501_;
v___y_2117_ = v___y_2450_;
v___y_2118_ = v___y_2451_;
v___y_2119_ = v___x_2499_;
v___y_2120_ = v___x_2477_;
v___y_2121_ = v___x_2611_;
v___y_2122_ = v___y_2458_;
v___y_2123_ = v___x_2555_;
v___y_2124_ = v___x_2486_;
v___y_2125_ = v___x_2609_;
v___y_2126_ = v___y_2461_;
v___y_2127_ = v___x_2517_;
v___y_2128_ = v___x_2616_;
v___y_2129_ = v___x_2503_;
v___y_2130_ = v___y_2446_;
v___y_2131_ = v___y_2447_;
v___y_2132_ = v___x_2557_;
v___y_2133_ = v___x_2540_;
v___y_2134_ = v___y_2449_;
v___y_2135_ = v___x_2478_;
v___y_2136_ = v___x_2539_;
v___y_2137_ = v___x_2485_;
v___y_2138_ = v___y_2453_;
v___y_2139_ = v___x_2481_;
v___y_2140_ = v___y_2454_;
v___y_2141_ = v___y_2455_;
v___y_2142_ = v___x_2486_;
v___y_2143_ = v___y_2457_;
v___y_2144_ = v___x_2471_;
v___y_2145_ = v___y_2459_;
v___y_2146_ = v___x_2516_;
v___y_2147_ = v___x_2610_;
v___y_2148_ = v___y_2460_;
v___y_2149_ = v___x_2630_;
goto v___jp_2111_;
}
}
}
}
}
else
{
uint8_t v___x_2633_; 
lean_del_object(v___x_1934_);
v___x_2633_ = l_Lean_Name_hasMacroScopes(v___x_2444_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1913_, v___x_2444_);
v___y_2393_ = v___y_2448_;
v___y_2394_ = v___x_2475_;
v___y_2395_ = v___x_2608_;
v___y_2396_ = v___x_2501_;
v___y_2397_ = v___y_2450_;
v___y_2398_ = v___y_2451_;
v___y_2399_ = v___x_2499_;
v___y_2400_ = v___x_2477_;
v___y_2401_ = v___y_2458_;
v___y_2402_ = v___x_2555_;
v___y_2403_ = v___x_2486_;
v___y_2404_ = v___x_2609_;
v___y_2405_ = v___y_2461_;
v___y_2406_ = v___x_2517_;
v___y_2407_ = v___x_2503_;
v___y_2408_ = v___y_2446_;
v___y_2409_ = v___y_2447_;
v___y_2410_ = v___x_2557_;
v___y_2411_ = v___x_2540_;
v___y_2412_ = v___y_2449_;
v___y_2413_ = v___x_2539_;
v___y_2414_ = v___x_2478_;
v___y_2415_ = v___x_2485_;
v___y_2416_ = v___y_2453_;
v___y_2417_ = v___x_2481_;
v___y_2418_ = v___y_2454_;
v___y_2419_ = v___y_2455_;
v___y_2420_ = v___x_2486_;
v___y_2421_ = v___y_2457_;
v___y_2422_ = v___x_2471_;
v___y_2423_ = v___y_2459_;
v___y_2424_ = v___x_2516_;
v___y_2425_ = v___y_2460_;
v___y_2426_ = v___x_2634_;
goto v___jp_2392_;
}
else
{
lean_object* v_view_2635_; lean_object* v_name_2636_; lean_object* v_imported_2637_; lean_object* v_ctx_2638_; lean_object* v_scopes_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2648_; 
v_view_2635_ = l_Lean_extractMacroScopes(v___x_2444_);
v_name_2636_ = lean_ctor_get(v_view_2635_, 0);
v_imported_2637_ = lean_ctor_get(v_view_2635_, 1);
v_ctx_2638_ = lean_ctor_get(v_view_2635_, 2);
v_scopes_2639_ = lean_ctor_get(v_view_2635_, 3);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_view_2635_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2641_ = v_view_2635_;
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_scopes_2639_);
lean_inc(v_ctx_2638_);
lean_inc(v_imported_2637_);
lean_inc(v_name_2636_);
lean_dec(v_view_2635_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___lam__2(v_structId_1913_, v_name_2636_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_imported_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_ctx_2638_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_scopes_2639_);
v___x_2645_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_MacroScopesView_review(v___x_2645_);
v___y_2393_ = v___y_2448_;
v___y_2394_ = v___x_2475_;
v___y_2395_ = v___x_2608_;
v___y_2396_ = v___x_2501_;
v___y_2397_ = v___y_2450_;
v___y_2398_ = v___y_2451_;
v___y_2399_ = v___x_2499_;
v___y_2400_ = v___x_2477_;
v___y_2401_ = v___y_2458_;
v___y_2402_ = v___x_2555_;
v___y_2403_ = v___x_2486_;
v___y_2404_ = v___x_2609_;
v___y_2405_ = v___y_2461_;
v___y_2406_ = v___x_2517_;
v___y_2407_ = v___x_2503_;
v___y_2408_ = v___y_2446_;
v___y_2409_ = v___y_2447_;
v___y_2410_ = v___x_2557_;
v___y_2411_ = v___x_2540_;
v___y_2412_ = v___y_2449_;
v___y_2413_ = v___x_2539_;
v___y_2414_ = v___x_2478_;
v___y_2415_ = v___x_2485_;
v___y_2416_ = v___y_2453_;
v___y_2417_ = v___x_2481_;
v___y_2418_ = v___y_2454_;
v___y_2419_ = v___y_2455_;
v___y_2420_ = v___x_2486_;
v___y_2421_ = v___y_2457_;
v___y_2422_ = v___x_2471_;
v___y_2423_ = v___y_2459_;
v___y_2424_ = v___x_2516_;
v___y_2425_ = v___y_2460_;
v___y_2426_ = v___x_2646_;
goto v___jp_2392_;
}
}
}
}
}
v___jp_2649_:
{
lean_object* v_methods_2651_; lean_object* v_quotContext_2652_; lean_object* v_currMacroScope_2653_; lean_object* v_currRecDepth_2654_; lean_object* v_maxRecDepth_2655_; lean_object* v_ref_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_methods_2651_ = lean_ctor_get(v___y_1918_, 0);
v_quotContext_2652_ = lean_ctor_get(v___y_1918_, 1);
v_currMacroScope_2653_ = lean_ctor_get(v___y_1918_, 2);
v_currRecDepth_2654_ = lean_ctor_get(v___y_1918_, 3);
v_maxRecDepth_2655_ = lean_ctor_get(v___y_1918_, 4);
v_ref_2656_ = lean_ctor_get(v___y_1918_, 5);
v___x_2657_ = l_Lean_mkIdentFrom(v_id_1937_, v___y_2650_, v___x_1930_);
v___x_2658_ = l_Lean_SourceInfo_fromRef(v_ref_2656_, v___x_1930_);
v___x_2659_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2660_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2661_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_2662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_2663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_2664_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2665_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
lean_inc(v___x_2658_);
v___x_2666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2658_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
lean_ctor_set(v___x_2666_, 2, v___x_2665_);
if (lean_obj_tag(v_vis_x3f_1912_) == 1)
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v_vis_x3f_1912_, 0);
lean_inc(v_val_2667_);
v___x_2668_ = l_Array_mkArray1___redArg(v_val_2667_);
v___y_2446_ = v___x_2662_;
v___y_2447_ = v___x_2657_;
v___y_2448_ = v_methods_2651_;
v___y_2449_ = v___x_2665_;
v___y_2450_ = v___x_2660_;
v___y_2451_ = v___x_2664_;
v___y_2452_ = v___x_2658_;
v___y_2453_ = v_quotContext_2652_;
v___y_2454_ = v___x_2661_;
v___y_2455_ = v_ref_2656_;
v___y_2456_ = v___x_2666_;
v___y_2457_ = v___x_2659_;
v___y_2458_ = v_currRecDepth_2654_;
v___y_2459_ = v___x_2663_;
v___y_2460_ = v_maxRecDepth_2655_;
v___y_2461_ = v_currMacroScope_2653_;
v___y_2462_ = v___x_2668_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2446_ = v___x_2662_;
v___y_2447_ = v___x_2657_;
v___y_2448_ = v_methods_2651_;
v___y_2449_ = v___x_2665_;
v___y_2450_ = v___x_2660_;
v___y_2451_ = v___x_2664_;
v___y_2452_ = v___x_2658_;
v___y_2453_ = v_quotContext_2652_;
v___y_2454_ = v___x_2661_;
v___y_2455_ = v_ref_2656_;
v___y_2456_ = v___x_2666_;
v___y_2457_ = v___x_2659_;
v___y_2458_ = v_currRecDepth_2654_;
v___y_2459_ = v___x_2663_;
v___y_2460_ = v_maxRecDepth_2655_;
v___y_2461_ = v_currMacroScope_2653_;
v___y_2462_ = v___x_2669_;
goto v___jp_2445_;
}
}
}
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v_b_1917_);
lean_ctor_set(v___x_2687_, 1, v___y_1919_);
return v___x_2687_;
}
v___jp_1920_:
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1915_, v___x_1923_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4(v_structTy_1910_, v___x_1911_, v_vis_x3f_1912_, v_structId_1913_, v_as_1914_, v___x_1924_, v_stop_1916_, v_a_1921_, v___y_1918_, v_a_1922_);
return v___x_1925_;
}
v___jp_1926_:
{
if (lean_obj_tag(v___y_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v_a_1929_; 
v_a_1928_ = lean_ctor_get(v___y_1927_, 0);
lean_inc(v_a_1928_);
v_a_1929_ = lean_ctor_get(v___y_1927_, 1);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___y_1927_, 2);
v_a_1921_ = v_a_1928_;
v_a_1922_ = v_a_1929_;
goto v___jp_1920_;
}
else
{
lean_dec(v_vis_x3f_1912_);
lean_dec(v___x_1911_);
lean_dec(v_structTy_1910_);
return v___y_1927_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_structTy_1910_ = stack[0].m_obj;
lean_object* v___x_1911_ = stack[1].m_obj;
lean_object* v_vis_x3f_1912_ = stack[2].m_obj;
lean_object* v_structId_1913_ = stack[3].m_obj;
lean_object* v_as_1914_ = stack[4].m_obj;
size_t v_i_1915_ = stack[5].m_num;
size_t v_stop_1916_ = stack[6].m_num;
lean_object* v_b_1917_ = stack[7].m_obj;
lean_object* v___y_1918_ = stack[8].m_obj;
lean_object* v___y_1919_ = stack[9].m_obj;
lean_object* v_res_2688_;
v_res_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_1910_, v___x_1911_, v_vis_x3f_1912_, v_structId_1913_, v_as_1914_, v_i_1915_, v_stop_1916_, v_b_1917_, v___y_1918_, v___y_1919_);
stack->m_obj
 = v_res_2688_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3___boxed(lean_object* v_structTy_2689_, lean_object* v___x_2690_, lean_object* v_vis_x3f_2691_, lean_object* v_structId_2692_, lean_object* v_as_2693_, lean_object* v_i_2694_, lean_object* v_stop_2695_, lean_object* v_b_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
size_t v_i_boxed_2699_; size_t v_stop_boxed_2700_; lean_object* v_res_2701_; 
v_i_boxed_2699_ = lean_unbox_usize(v_i_2694_);
lean_dec(v_i_2694_);
v_stop_boxed_2700_ = lean_unbox_usize(v_stop_2695_);
lean_dec(v_stop_2695_);
v_res_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2689_, v___x_2690_, v_vis_x3f_2691_, v_structId_2692_, v_as_2693_, v_i_boxed_2699_, v_stop_boxed_2700_, v_b_2696_, v___y_2697_, v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec_ref(v_as_2693_);
lean_dec(v_structId_2692_);
return v_res_2701_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(size_t v_sz_2702_, size_t v_i_2703_, lean_object* v_bs_2704_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_usize_dec_lt(v_i_2703_, v_sz_2702_);
if (v___x_2705_ == 0)
{
return v_bs_2704_;
}
else
{
lean_object* v_v_2706_; lean_object* v_id_2707_; lean_object* v___x_2708_; lean_object* v_bs_x27_2709_; size_t v___x_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v_v_2706_ = lean_array_uget_borrowed(v_bs_2704_, v_i_2703_);
v_id_2707_ = lean_ctor_get(v_v_2706_, 2);
lean_inc(v_id_2707_);
v___x_2708_ = lean_unsigned_to_nat(0u);
v_bs_x27_2709_ = lean_array_uset(v_bs_2704_, v_i_2703_, v___x_2708_);
v___x_2710_ = ((size_t)1ULL);
v___x_2711_ = lean_usize_add(v_i_2703_, v___x_2710_);
v___x_2712_ = lean_array_uset(v_bs_x27_2709_, v_i_2703_, v_id_2707_);
v_i_2703_ = v___x_2711_;
v_bs_2704_ = v___x_2712_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2702_ = stack[0].m_num;
size_t v_i_2703_ = stack[1].m_num;
lean_object* v_bs_2704_ = stack[2].m_obj;
lean_object* v_res_2714_;
v_res_2714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_2702_, v_i_2703_, v_bs_2704_);
stack->m_obj
 = v_res_2714_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0___boxed(lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_bs_2717_){
_start:
{
size_t v_sz_boxed_2718_; size_t v_i_boxed_2719_; lean_object* v_res_2720_; 
v_sz_boxed_2718_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2719_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_boxed_2718_, v_i_boxed_2719_, v_bs_2717_);
return v_res_2720_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = l_Lean_firstFrontendMacroScope;
v___x_2730_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__4));
v___x_2731_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__1));
v___x_2732_ = l_Lean_addMacroScope(v___x_2731_, v___x_2730_, v___x_2729_);
return v___x_2732_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__7));
v___x_2737_ = l_String_toRawSubstring_x27(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2744_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__10));
v___x_2745_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__5);
v___x_2746_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__8);
v___x_2747_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_2748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___x_2746_);
lean_ctor_set(v___x_2748_, 2, v___x_2745_);
lean_ctor_set(v___x_2748_, 3, v___x_2744_);
return v___x_2748_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v_data_2751_; 
v___x_2749_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__11);
v___x_2750_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v_data_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_data_2751_, 0, v___x_2750_);
lean_ctor_set(v_data_2751_, 1, v___x_2749_);
return v_data_2751_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2763_ = l_Lean_mkAtom(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__18));
v___x_2772_ = l_String_toRawSubstring_x27(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_2794_ = l_String_toRawSubstring_x27(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__20));
v___x_2804_ = l_String_toRawSubstring_x27(v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__37));
v___x_2814_ = l_String_toRawSubstring_x27(v___x_2813_);
return v___x_2814_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__40));
v___x_2819_ = l_Lean_mkAtom(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2820_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2821_ = lean_unsigned_to_nat(3u);
v___x_2822_ = lean_mk_empty_array_with_capacity(v___x_2821_);
v___x_2823_ = lean_array_push(v___x_2822_, v___x_2820_);
return v___x_2823_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__41);
v___x_2825_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__42);
v___x_2826_ = lean_array_push(v___x_2825_, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__19));
v___x_2843_ = l_String_toRawSubstring_x27(v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(lean_object* v_vis_x3f_2870_, lean_object* v_structId_2871_, lean_object* v_structArity_2872_, lean_object* v_structTy_2873_, lean_object* v_views_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_quotContext_2877_; lean_object* v_currMacroScope_2878_; lean_object* v_ref_2879_; lean_object* v___x_2880_; lean_object* v_a_2881_; lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_3372_; 
v_quotContext_2877_ = lean_ctor_get(v_a_2875_, 1);
v_currMacroScope_2878_ = lean_ctor_get(v_a_2875_, 2);
v_ref_2879_ = lean_ctor_get(v_a_2875_, 5);
v___x_2880_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v_a_2876_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_a_2882_ = lean_ctor_get(v___x_2880_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_2884_ = v___x_2880_;
v_isShared_2885_ = v_isSharedCheck_3372_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_3372_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v_data_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; size_t v_sz_2899_; size_t v___x_2900_; lean_object* v___x_2901_; size_t v_sz_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v_a_3331_; lean_object* v_a_3332_; lean_object* v___y_3351_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = 0;
v___x_2888_ = lean_box(0);
v_data_2889_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__12);
v___x_2890_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_2891_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_2892_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__13));
v___x_2893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__26));
lean_inc_n(v_a_2881_, 9);
v___x_2894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_a_2881_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_2896_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v___x_2897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2897_, 0, v_a_2881_);
lean_ctor_set(v___x_2897_, 1, v___x_2895_);
lean_ctor_set(v___x_2897_, 2, v___x_2896_);
v___x_2898_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__14));
v_sz_2899_ = lean_array_size(v_views_2874_);
v___x_2900_ = ((size_t)0ULL);
lean_inc_ref(v_views_2874_);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__0(v_sz_2899_, v___x_2900_, v_views_2874_);
v_sz_2902_ = lean_array_size(v___x_2901_);
lean_inc_ref_n(v___x_2897_, 2);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1(v_a_2881_, v___x_2897_, v_sz_2902_, v___x_2900_, v___x_2901_);
v___x_2904_ = ((lean_object*)(l_Lake_configField___closed__21));
v___x_2905_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__15);
v___x_2906_ = l_Lean_mkSepArray(v___x_2903_, v___x_2905_);
lean_dec_ref(v___x_2903_);
v___x_2907_ = l_Array_append___redArg(v___x_2896_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2881_);
lean_ctor_set(v___x_2908_, 1, v___x_2895_);
lean_ctor_set(v___x_2908_, 2, v___x_2907_);
v___x_2909_ = l_Lean_Syntax_node1(v_a_2881_, v___x_2898_, v___x_2908_);
v___x_2910_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__16));
v___x_2911_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__17));
v___x_2912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2881_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_Syntax_node1(v_a_2881_, v___x_2895_, v___x_2912_);
v___x_2914_ = l_Lean_Syntax_node1(v_a_2881_, v___x_2910_, v___x_2913_);
v___x_2915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__51));
v___x_3363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_a_2881_);
lean_ctor_set(v___x_3363_, 1, v___x_2915_);
v___x_3364_ = l_Lean_Syntax_node6(v_a_2881_, v___x_2892_, v___x_2894_, v___x_2897_, v___x_2909_, v___x_2914_, v___x_2897_, v___x_3363_);
v___x_3365_ = lean_array_get_size(v_views_2874_);
v___x_3366_ = lean_nat_dec_lt(v___x_2886_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_dec(v___x_3364_);
lean_dec_ref(v_views_2874_);
v_a_3331_ = v_data_2889_;
v_a_3332_ = v_a_2882_;
goto v___jp_3330_;
}
else
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_nat_dec_le(v___x_3365_, v___x_3365_);
if (v___x_3367_ == 0)
{
if (v___x_3366_ == 0)
{
lean_dec(v___x_3364_);
lean_dec_ref(v_views_2874_);
v_a_3331_ = v_data_2889_;
v_a_3332_ = v_a_2882_;
goto v___jp_3330_;
}
else
{
size_t v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_usize_of_nat(v___x_3365_);
lean_inc(v_vis_x3f_2870_);
lean_inc(v_structTy_2873_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2873_, v___x_3364_, v_vis_x3f_2870_, v_structId_2871_, v_views_2874_, v___x_2900_, v___x_3368_, v_data_2889_, v_a_2875_, v_a_2882_);
lean_dec_ref(v_views_2874_);
v___y_3351_ = v___x_3369_;
goto v___jp_3350_;
}
}
else
{
size_t v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = lean_usize_of_nat(v___x_3365_);
lean_inc(v_vis_x3f_2870_);
lean_inc(v_structTy_2873_);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3(v_structTy_2873_, v___x_3364_, v_vis_x3f_2870_, v_structId_2871_, v_views_2874_, v___x_2900_, v___x_3370_, v_data_2889_, v_a_2875_, v_a_2882_);
lean_dec_ref(v_views_2874_);
v___y_3351_ = v___x_3371_;
goto v___jp_3350_;
}
}
v___jp_2916_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2942_ = l_Array_append___redArg(v___x_2896_, v___y_2941_);
lean_dec_ref(v___y_2941_);
lean_inc_n(v___y_2923_, 27);
v___x_2943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2943_, 0, v___y_2923_);
lean_ctor_set(v___x_2943_, 1, v___x_2895_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
lean_inc_n(v___y_2922_, 16);
lean_inc(v___y_2928_);
v___x_2944_ = l_Lean_Syntax_node7(v___y_2923_, v___y_2928_, v___y_2922_, v___y_2922_, v___x_2943_, v___y_2922_, v___y_2922_, v___y_2922_, v___y_2922_);
v___x_2945_ = l_Lean_Syntax_node1(v___y_2923_, v___y_2926_, v___y_2922_);
v___x_2946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___y_2923_);
lean_ctor_set(v___x_2946_, 1, v___y_2930_);
v___x_2947_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2939_, v___y_2937_, v___y_2922_);
v___x_2948_ = l_Lean_Syntax_node1(v___y_2923_, v___x_2895_, v___x_2947_);
lean_inc_ref(v___y_2931_);
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___y_2923_);
lean_ctor_set(v___x_2949_, 1, v___y_2931_);
v___x_2950_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__19);
v___x_2951_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__20));
lean_inc(v_currMacroScope_2878_);
lean_inc(v_quotContext_2877_);
v___x_2952_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_2951_, v_currMacroScope_2878_);
v___x_2953_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__24));
v___x_2954_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2954_, 0, v___y_2923_);
lean_ctor_set(v___x_2954_, 1, v___x_2950_);
lean_ctor_set(v___x_2954_, 2, v___x_2952_);
lean_ctor_set(v___x_2954_, 3, v___x_2953_);
v___x_2955_ = l_Lean_Syntax_node1(v___y_2923_, v___x_2895_, v_structTy_2873_);
v___x_2956_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2933_, v___x_2954_, v___x_2955_);
v___x_2957_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2938_, v___x_2949_, v___x_2956_);
v___x_2958_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2932_, v___y_2922_, v___x_2957_);
lean_inc_ref(v___y_2925_);
v___x_2959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___y_2923_);
lean_ctor_set(v___x_2959_, 1, v___y_2925_);
lean_inc_ref(v___y_2920_);
v___x_2960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___y_2923_);
lean_ctor_set(v___x_2960_, 1, v___y_2920_);
v___x_2961_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__26));
v___x_2962_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__28));
v___x_2963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___y_2923_);
lean_ctor_set(v___x_2963_, 1, v___x_2893_);
v___x_2964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___y_2923_);
lean_ctor_set(v___x_2964_, 1, v___x_2915_);
lean_inc_ref(v___x_2964_);
lean_inc_ref(v___x_2963_);
v___x_2965_ = l_Lean_Syntax_node2(v___y_2923_, v___x_2962_, v___x_2963_, v___x_2964_);
v___x_2966_ = l_Lean_Syntax_node1(v___y_2923_, v___x_2898_, v___y_2922_);
v___x_2967_ = l_Lean_Syntax_node1(v___y_2923_, v___x_2910_, v___y_2922_);
v___x_2968_ = l_Lean_Syntax_node6(v___y_2923_, v___x_2892_, v___x_2963_, v___y_2922_, v___x_2966_, v___x_2967_, v___y_2922_, v___x_2964_);
v___x_2969_ = l_Lean_Syntax_node2(v___y_2923_, v___x_2961_, v___x_2965_, v___x_2968_);
v___x_2970_ = l_Lean_Syntax_node1(v___y_2923_, v___x_2895_, v___x_2969_);
lean_inc_ref(v___y_2917_);
v___x_2971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2923_);
lean_ctor_set(v___x_2971_, 1, v___y_2917_);
v___x_2972_ = l_Lean_Syntax_node3(v___y_2923_, v___y_2935_, v___x_2960_, v___x_2970_, v___x_2971_);
v___x_2973_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2918_, v___y_2922_, v___y_2922_);
v___x_2974_ = l_Lean_Syntax_node4(v___y_2923_, v___y_2940_, v___x_2959_, v___x_2972_, v___x_2973_, v___y_2922_);
v___x_2975_ = l_Lean_Syntax_node6(v___y_2923_, v___y_2936_, v___x_2945_, v___x_2946_, v___y_2922_, v___x_2948_, v___x_2958_, v___x_2974_);
lean_inc(v___y_2921_);
v___x_2976_ = l_Lean_Syntax_node2(v___y_2923_, v___y_2921_, v___x_2944_, v___x_2975_);
v___x_2977_ = lean_array_push(v___y_2919_, v___y_2929_);
v___x_2978_ = lean_array_push(v___x_2977_, v___y_2927_);
v___x_2979_ = lean_array_push(v___x_2978_, v___y_2924_);
v___x_2980_ = lean_array_push(v___x_2979_, v___x_2976_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 1, v___y_2934_);
lean_ctor_set(v___x_2884_, 0, v___x_2980_);
v___x_2982_ = v___x_2884_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___y_2934_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
v___jp_2984_:
{
lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3007_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v___y_2987_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_n(v_a_3008_, 2);
v_a_3009_ = lean_ctor_get(v___x_3007_, 1);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3007_);
v___x_3010_ = l_Lean_mkIdentFrom(v_structId_2871_, v___y_3006_, v___x_2887_);
lean_dec(v_structId_2871_);
v___x_3011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3011_, 0, v_a_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_2895_);
lean_ctor_set(v___x_3011_, 2, v___x_2896_);
if (lean_obj_tag(v_vis_x3f_2870_) == 1)
{
lean_object* v_val_3012_; lean_object* v___x_3013_; 
v_val_3012_ = lean_ctor_get(v_vis_x3f_2870_, 0);
lean_inc(v_val_3012_);
lean_dec_ref_known(v_vis_x3f_2870_, 1);
v___x_3013_ = l_Array_mkArray1___redArg(v_val_3012_);
v___y_2917_ = v___y_2985_;
v___y_2918_ = v___y_2986_;
v___y_2919_ = v___y_2988_;
v___y_2920_ = v___y_2989_;
v___y_2921_ = v___y_2990_;
v___y_2922_ = v___x_3011_;
v___y_2923_ = v_a_3008_;
v___y_2924_ = v___y_2991_;
v___y_2925_ = v___y_2992_;
v___y_2926_ = v___y_2993_;
v___y_2927_ = v___y_2994_;
v___y_2928_ = v___y_2995_;
v___y_2929_ = v___y_2996_;
v___y_2930_ = v___y_2997_;
v___y_2931_ = v___y_2999_;
v___y_2932_ = v___y_2998_;
v___y_2933_ = v___y_3000_;
v___y_2934_ = v_a_3009_;
v___y_2935_ = v___y_3001_;
v___y_2936_ = v___y_3002_;
v___y_2937_ = v___x_3010_;
v___y_2938_ = v___y_3003_;
v___y_2939_ = v___y_3004_;
v___y_2940_ = v___y_3005_;
v___y_2941_ = v___x_3013_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_3014_; 
lean_dec(v_vis_x3f_2870_);
v___x_3014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_2917_ = v___y_2985_;
v___y_2918_ = v___y_2986_;
v___y_2919_ = v___y_2988_;
v___y_2920_ = v___y_2989_;
v___y_2921_ = v___y_2990_;
v___y_2922_ = v___x_3011_;
v___y_2923_ = v_a_3008_;
v___y_2924_ = v___y_2991_;
v___y_2925_ = v___y_2992_;
v___y_2926_ = v___y_2993_;
v___y_2927_ = v___y_2994_;
v___y_2928_ = v___y_2995_;
v___y_2929_ = v___y_2996_;
v___y_2930_ = v___y_2997_;
v___y_2931_ = v___y_2999_;
v___y_2932_ = v___y_2998_;
v___y_2933_ = v___y_3000_;
v___y_2934_ = v_a_3009_;
v___y_2935_ = v___y_3001_;
v___y_2936_ = v___y_3002_;
v___y_2937_ = v___x_3010_;
v___y_2938_ = v___y_3003_;
v___y_2939_ = v___y_3004_;
v___y_2940_ = v___y_3005_;
v___y_2941_ = v___x_3014_;
goto v___jp_2916_;
}
}
v___jp_3015_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3044_ = l_Array_append___redArg(v___x_2896_, v___y_3043_);
lean_dec_ref(v___y_3043_);
lean_inc_n(v___y_3017_, 16);
v___x_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___y_3017_);
lean_ctor_set(v___x_3045_, 1, v___x_2895_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
lean_inc_n(v___y_3024_, 12);
lean_inc(v___y_3025_);
v___x_3046_ = l_Lean_Syntax_node7(v___y_3017_, v___y_3025_, v___y_3024_, v___y_3024_, v___x_3045_, v___y_3024_, v___y_3024_, v___y_3024_, v___y_3024_);
lean_inc(v___y_3035_);
v___x_3047_ = l_Lean_Syntax_node1(v___y_3017_, v___y_3035_, v___y_3024_);
lean_inc_ref(v___y_3026_);
v___x_3048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___y_3017_);
lean_ctor_set(v___x_3048_, 1, v___y_3026_);
lean_inc(v___y_3041_);
v___x_3049_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3041_, v___y_3023_, v___y_3024_);
v___x_3050_ = l_Lean_Syntax_node1(v___y_3017_, v___x_2895_, v___x_3049_);
lean_inc_ref(v___y_3037_);
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3017_);
lean_ctor_set(v___x_3051_, 1, v___y_3037_);
v___x_3052_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__29));
v___x_3053_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__30);
v___x_3054_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__31));
lean_inc(v_currMacroScope_2878_);
lean_inc(v_quotContext_2877_);
v___x_3055_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_3054_, v_currMacroScope_2878_);
lean_inc_ref(v___y_3020_);
v___x_3056_ = l_Lean_Name_mkStr2(v___y_3020_, v___x_3052_);
lean_inc(v___x_3056_);
v___x_3057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_2888_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
v___x_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_2888_);
v___x_3060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3057_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3061_, 0, v___y_3017_);
lean_ctor_set(v___x_3061_, 1, v___x_3053_);
lean_ctor_set(v___x_3061_, 2, v___x_3055_);
lean_ctor_set(v___x_3061_, 3, v___x_3060_);
v___x_3062_ = l_Lean_Syntax_node1(v___y_3017_, v___x_2895_, v___y_3034_);
lean_inc(v___y_3029_);
v___x_3063_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3029_, v___x_3061_, v___x_3062_);
lean_inc(v___y_3040_);
v___x_3064_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3040_, v___x_3051_, v___x_3063_);
lean_inc(v___y_3028_);
v___x_3065_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3028_, v___y_3024_, v___x_3064_);
lean_inc_ref(v___y_3021_);
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3017_);
lean_ctor_set(v___x_3066_, 1, v___y_3021_);
lean_inc(v___y_3030_);
v___x_3067_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3030_, v___y_3024_, v___y_3024_);
lean_inc(v___y_3042_);
v___x_3068_ = l_Lean_Syntax_node4(v___y_3017_, v___y_3042_, v___x_3066_, v___y_3022_, v___x_3067_, v___y_3024_);
lean_inc(v___y_3039_);
v___x_3069_ = l_Lean_Syntax_node6(v___y_3017_, v___y_3039_, v___x_3047_, v___x_3048_, v___y_3024_, v___x_3050_, v___x_3065_, v___x_3068_);
lean_inc(v___y_3019_);
v___x_3070_ = l_Lean_Syntax_node2(v___y_3017_, v___y_3019_, v___x_3046_, v___x_3069_);
v___x_3071_ = l_Lean_Name_hasMacroScopes(v___y_3033_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v___y_3033_);
v___y_2985_ = v___y_3016_;
v___y_2986_ = v___y_3030_;
v___y_2987_ = v___y_3031_;
v___y_2988_ = v___y_3018_;
v___y_2989_ = v___y_3032_;
v___y_2990_ = v___y_3019_;
v___y_2991_ = v___x_3070_;
v___y_2992_ = v___y_3021_;
v___y_2993_ = v___y_3035_;
v___y_2994_ = v___y_3036_;
v___y_2995_ = v___y_3025_;
v___y_2996_ = v___y_3027_;
v___y_2997_ = v___y_3026_;
v___y_2998_ = v___y_3028_;
v___y_2999_ = v___y_3037_;
v___y_3000_ = v___y_3029_;
v___y_3001_ = v___y_3038_;
v___y_3002_ = v___y_3039_;
v___y_3003_ = v___y_3040_;
v___y_3004_ = v___y_3041_;
v___y_3005_ = v___y_3042_;
v___y_3006_ = v___x_3072_;
goto v___jp_2984_;
}
else
{
lean_object* v_view_3073_; lean_object* v_name_3074_; lean_object* v_imported_3075_; lean_object* v_ctx_3076_; lean_object* v_scopes_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3086_; 
v_view_3073_ = l_Lean_extractMacroScopes(v___y_3033_);
v_name_3074_ = lean_ctor_get(v_view_3073_, 0);
v_imported_3075_ = lean_ctor_get(v_view_3073_, 1);
v_ctx_3076_ = lean_ctor_get(v_view_3073_, 2);
v_scopes_3077_ = lean_ctor_get(v_view_3073_, 3);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_view_3073_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3079_ = v_view_3073_;
v_isShared_3080_ = v_isSharedCheck_3086_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_scopes_3077_);
lean_inc(v_ctx_3076_);
lean_inc(v_imported_3075_);
lean_inc(v_name_3074_);
lean_dec(v_view_3073_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3086_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3081_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__4(v_name_3074_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 0, v___x_3081_);
v___x_3083_ = v___x_3079_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_imported_3075_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_ctx_3076_);
lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_scopes_3077_);
v___x_3083_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_MacroScopesView_review(v___x_3083_);
v___y_2985_ = v___y_3016_;
v___y_2986_ = v___y_3030_;
v___y_2987_ = v___y_3031_;
v___y_2988_ = v___y_3018_;
v___y_2989_ = v___y_3032_;
v___y_2990_ = v___y_3019_;
v___y_2991_ = v___x_3070_;
v___y_2992_ = v___y_3021_;
v___y_2993_ = v___y_3035_;
v___y_2994_ = v___y_3036_;
v___y_2995_ = v___y_3025_;
v___y_2996_ = v___y_3027_;
v___y_2997_ = v___y_3026_;
v___y_2998_ = v___y_3028_;
v___y_2999_ = v___y_3037_;
v___y_3000_ = v___y_3029_;
v___y_3001_ = v___y_3038_;
v___y_3002_ = v___y_3039_;
v___y_3003_ = v___y_3040_;
v___y_3004_ = v___y_3041_;
v___y_3005_ = v___y_3042_;
v___y_3006_ = v___x_3084_;
goto v___jp_2984_;
}
}
}
}
v___jp_3087_:
{
lean_object* v___x_3112_; lean_object* v_a_3113_; lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3163_; 
v___x_3112_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v___y_3096_);
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_a_3114_ = lean_ctor_get(v___x_3112_, 1);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3116_ = v___x_3112_;
v_isShared_3117_ = v_isSharedCheck_3163_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3163_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__33));
lean_inc(v_a_3113_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 2);
lean_ctor_set(v___x_3116_, 1, v___x_2893_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3113_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_2893_);
v___x_3120_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc_n(v_a_3113_, 17);
v___x_3121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3121_, 0, v_a_3113_);
lean_ctor_set(v___x_3121_, 1, v___x_2895_);
lean_ctor_set(v___x_3121_, 2, v___x_2896_);
v___x_3122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__1___closed__1));
v___x_3123_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__2));
v___x_3124_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__34);
v___x_3125_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__35));
lean_inc_n(v_currMacroScope_2878_, 2);
lean_inc_n(v_quotContext_2877_, 2);
v___x_3126_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_3125_, v_currMacroScope_2878_);
v___x_3127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3127_, 0, v_a_3113_);
lean_ctor_set(v___x_3127_, 1, v___x_3124_);
lean_ctor_set(v___x_3127_, 2, v___x_3126_);
lean_ctor_set(v___x_3127_, 3, v___x_2888_);
lean_inc_ref_n(v___x_3121_, 10);
v___x_3128_ = l_Lean_Syntax_node2(v_a_3113_, v___x_3123_, v___x_3127_, v___x_3121_);
v___x_3129_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__36));
lean_inc_ref(v___y_3094_);
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3113_);
lean_ctor_set(v___x_3130_, 1, v___y_3094_);
lean_inc_ref(v___x_3130_);
v___x_3131_ = l_Lean_Syntax_node3(v_a_3113_, v___x_3129_, v___x_3130_, v___x_3121_, v___y_3097_);
v___x_3132_ = l_Lean_Syntax_node3(v_a_3113_, v___x_2895_, v___x_3121_, v___x_3121_, v___x_3131_);
v___x_3133_ = l_Lean_Syntax_node2(v_a_3113_, v___x_3122_, v___x_3128_, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_a_3113_);
lean_ctor_set(v___x_3134_, 1, v___x_2904_);
v___x_3135_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__38);
v___x_3136_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__39));
v___x_3137_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_3136_, v_currMacroScope_2878_);
v___x_3138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3138_, 0, v_a_3113_);
lean_ctor_set(v___x_3138_, 1, v___x_3135_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
lean_ctor_set(v___x_3138_, 3, v___x_2888_);
v___x_3139_ = l_Lean_Syntax_node2(v_a_3113_, v___x_3123_, v___x_3138_, v___x_3121_);
v___x_3140_ = l_Nat_reprFast(v_structArity_2872_);
v___x_3141_ = lean_box(2);
v___x_3142_ = l_Lean_Syntax_mkNumLit(v___x_3140_, v___x_3141_);
v___x_3143_ = l_Lean_Syntax_node3(v_a_3113_, v___x_3129_, v___x_3130_, v___x_3121_, v___x_3142_);
v___x_3144_ = l_Lean_Syntax_node3(v_a_3113_, v___x_2895_, v___x_3121_, v___x_3121_, v___x_3143_);
v___x_3145_ = l_Lean_Syntax_node2(v_a_3113_, v___x_3122_, v___x_3139_, v___x_3144_);
v___x_3146_ = l_Lean_Syntax_node3(v_a_3113_, v___x_2895_, v___x_3133_, v___x_3134_, v___x_3145_);
v___x_3147_ = l_Lean_Syntax_node1(v_a_3113_, v___x_2898_, v___x_3146_);
v___x_3148_ = l_Lean_Syntax_node1(v_a_3113_, v___x_2910_, v___x_3121_);
v___x_3149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_a_3113_);
lean_ctor_set(v___x_3149_, 1, v___x_2915_);
v___x_3150_ = l_Lean_Syntax_node6(v_a_3113_, v___x_2892_, v___x_3120_, v___x_3121_, v___x_3147_, v___x_3148_, v___x_3121_, v___x_3149_);
v___x_3151_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v_a_3114_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_n(v_a_3152_, 2);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3151_);
v___x_3154_ = l_Lean_mkIdentFrom(v_structId_2871_, v___y_3111_, v___x_2887_);
v___x_3155_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__43);
lean_inc(v_structId_2871_);
v___x_3156_ = lean_array_push(v___x_3155_, v_structId_2871_);
v___x_3157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3141_);
lean_ctor_set(v___x_3157_, 1, v___x_3118_);
lean_ctor_set(v___x_3157_, 2, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3158_, 0, v_a_3152_);
lean_ctor_set(v___x_3158_, 1, v___x_2895_);
lean_ctor_set(v___x_3158_, 2, v___x_2896_);
if (lean_obj_tag(v_vis_x3f_2870_) == 1)
{
lean_object* v_val_3159_; lean_object* v___x_3160_; 
v_val_3159_ = lean_ctor_get(v_vis_x3f_2870_, 0);
lean_inc(v_val_3159_);
v___x_3160_ = l_Array_mkArray1___redArg(v_val_3159_);
v___y_3016_ = v___y_3088_;
v___y_3017_ = v_a_3152_;
v___y_3018_ = v___y_3090_;
v___y_3019_ = v___y_3092_;
v___y_3020_ = v___y_3095_;
v___y_3021_ = v___y_3094_;
v___y_3022_ = v___x_3150_;
v___y_3023_ = v___x_3154_;
v___y_3024_ = v___x_3158_;
v___y_3025_ = v___y_3100_;
v___y_3026_ = v___y_3101_;
v___y_3027_ = v___y_3102_;
v___y_3028_ = v___y_3104_;
v___y_3029_ = v___y_3105_;
v___y_3030_ = v___y_3089_;
v___y_3031_ = v_a_3153_;
v___y_3032_ = v___y_3091_;
v___y_3033_ = v___y_3093_;
v___y_3034_ = v___x_3157_;
v___y_3035_ = v___y_3098_;
v___y_3036_ = v___y_3099_;
v___y_3037_ = v___y_3103_;
v___y_3038_ = v___y_3106_;
v___y_3039_ = v___y_3107_;
v___y_3040_ = v___y_3108_;
v___y_3041_ = v___y_3109_;
v___y_3042_ = v___y_3110_;
v___y_3043_ = v___x_3160_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3016_ = v___y_3088_;
v___y_3017_ = v_a_3152_;
v___y_3018_ = v___y_3090_;
v___y_3019_ = v___y_3092_;
v___y_3020_ = v___y_3095_;
v___y_3021_ = v___y_3094_;
v___y_3022_ = v___x_3150_;
v___y_3023_ = v___x_3154_;
v___y_3024_ = v___x_3158_;
v___y_3025_ = v___y_3100_;
v___y_3026_ = v___y_3101_;
v___y_3027_ = v___y_3102_;
v___y_3028_ = v___y_3104_;
v___y_3029_ = v___y_3105_;
v___y_3030_ = v___y_3089_;
v___y_3031_ = v_a_3153_;
v___y_3032_ = v___y_3091_;
v___y_3033_ = v___y_3093_;
v___y_3034_ = v___x_3157_;
v___y_3035_ = v___y_3098_;
v___y_3036_ = v___y_3099_;
v___y_3037_ = v___y_3103_;
v___y_3038_ = v___y_3106_;
v___y_3039_ = v___y_3107_;
v___y_3040_ = v___y_3108_;
v___y_3041_ = v___y_3109_;
v___y_3042_ = v___y_3110_;
v___y_3043_ = v___x_3161_;
goto v___jp_3015_;
}
}
}
}
v___jp_3164_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3181_ = l_Array_append___redArg(v___x_2896_, v___y_3180_);
lean_dec_ref(v___y_3180_);
lean_inc_n(v___y_3176_, 20);
v___x_3182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3182_, 0, v___y_3176_);
lean_ctor_set(v___x_3182_, 1, v___x_2895_);
lean_ctor_set(v___x_3182_, 2, v___x_3181_);
lean_inc_n(v___y_3168_, 12);
lean_inc(v___y_3174_);
v___x_3183_ = l_Lean_Syntax_node7(v___y_3176_, v___y_3174_, v___y_3168_, v___y_3168_, v___x_3182_, v___y_3168_, v___y_3168_, v___y_3168_, v___y_3168_);
v___x_3184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__0));
lean_inc_ref_n(v___y_3177_, 2);
v___x_3185_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3177_, v___x_3184_);
v___x_3186_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__44));
v___x_3187_ = l_Lean_Syntax_node1(v___y_3176_, v___x_3186_, v___y_3168_);
v___x_3188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___y_3176_);
lean_ctor_set(v___x_3188_, 1, v___x_3184_);
lean_inc(v___y_3178_);
v___x_3189_ = l_Lean_Syntax_node2(v___y_3176_, v___y_3178_, v___y_3173_, v___y_3168_);
v___x_3190_ = l_Lean_Syntax_node1(v___y_3176_, v___x_2895_, v___x_3189_);
v___x_3191_ = ((lean_object*)(l_Lake_configField___closed__27));
v___x_3192_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3177_, v___x_3191_);
v___x_3193_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
v___x_3194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___y_3176_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
v___x_3197_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47, &l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47_once, _init_l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__47);
v___x_3198_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__48));
lean_inc(v_currMacroScope_2878_);
lean_inc(v_quotContext_2877_);
v___x_3199_ = l_Lean_addMacroScope(v_quotContext_2877_, v___x_3198_, v_currMacroScope_2878_);
v___x_3200_ = ((lean_object*)(l_Lake_configField___closed__1));
v___x_3201_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__53));
v___x_3202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3176_);
lean_ctor_set(v___x_3202_, 1, v___x_3197_);
lean_ctor_set(v___x_3202_, 2, v___x_3199_);
lean_ctor_set(v___x_3202_, 3, v___x_3201_);
lean_inc(v_structTy_2873_);
v___x_3203_ = l_Lean_Syntax_node1(v___y_3176_, v___x_2895_, v_structTy_2873_);
v___x_3204_ = l_Lean_Syntax_node2(v___y_3176_, v___x_3196_, v___x_3202_, v___x_3203_);
v___x_3205_ = l_Lean_Syntax_node2(v___y_3176_, v___x_3193_, v___x_3195_, v___x_3204_);
lean_inc(v___x_3192_);
v___x_3206_ = l_Lean_Syntax_node2(v___y_3176_, v___x_3192_, v___y_3168_, v___x_3205_);
lean_inc_ref(v___y_3170_);
v___x_3207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3176_);
lean_ctor_set(v___x_3207_, 1, v___y_3170_);
v___x_3208_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__54));
v___x_3209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__16));
v___x_3210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___y_3176_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
lean_inc(v___y_3172_);
v___x_3211_ = l_Lean_Syntax_node1(v___y_3176_, v___x_2895_, v___y_3172_);
v___x_3212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__17));
v___x_3213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___y_3176_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_Syntax_node3(v___y_3176_, v___x_3208_, v___x_3210_, v___x_3211_, v___x_3213_);
lean_inc(v___y_3165_);
v___x_3215_ = l_Lean_Syntax_node2(v___y_3176_, v___y_3165_, v___y_3168_, v___y_3168_);
lean_inc(v___y_3179_);
v___x_3216_ = l_Lean_Syntax_node4(v___y_3176_, v___y_3179_, v___x_3207_, v___x_3214_, v___x_3215_, v___y_3168_);
lean_inc(v___x_3185_);
v___x_3217_ = l_Lean_Syntax_node6(v___y_3176_, v___x_3185_, v___x_3187_, v___x_3188_, v___y_3168_, v___x_3190_, v___x_3206_, v___x_3216_);
lean_inc(v___y_3167_);
v___x_3218_ = l_Lean_Syntax_node2(v___y_3176_, v___y_3167_, v___x_3183_, v___x_3217_);
v___x_3219_ = l_Lean_Name_hasMacroScopes(v___y_3169_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_inc(v___y_3169_);
v___x_3220_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v___y_3169_);
v___y_3088_ = v___x_3212_;
v___y_3089_ = v___y_3165_;
v___y_3090_ = v___y_3166_;
v___y_3091_ = v___x_3209_;
v___y_3092_ = v___y_3167_;
v___y_3093_ = v___y_3169_;
v___y_3094_ = v___y_3170_;
v___y_3095_ = v___x_3200_;
v___y_3096_ = v___y_3171_;
v___y_3097_ = v___y_3172_;
v___y_3098_ = v___x_3186_;
v___y_3099_ = v___x_3218_;
v___y_3100_ = v___y_3174_;
v___y_3101_ = v___x_3184_;
v___y_3102_ = v___y_3175_;
v___y_3103_ = v___x_3194_;
v___y_3104_ = v___x_3192_;
v___y_3105_ = v___x_3196_;
v___y_3106_ = v___x_3208_;
v___y_3107_ = v___x_3185_;
v___y_3108_ = v___x_3193_;
v___y_3109_ = v___y_3178_;
v___y_3110_ = v___y_3179_;
v___y_3111_ = v___x_3220_;
goto v___jp_3087_;
}
else
{
lean_object* v_view_3221_; lean_object* v_name_3222_; lean_object* v_imported_3223_; lean_object* v_ctx_3224_; lean_object* v_scopes_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3234_; 
lean_inc(v___y_3169_);
v_view_3221_ = l_Lean_extractMacroScopes(v___y_3169_);
v_name_3222_ = lean_ctor_get(v_view_3221_, 0);
v_imported_3223_ = lean_ctor_get(v_view_3221_, 1);
v_ctx_3224_ = lean_ctor_get(v_view_3221_, 2);
v_scopes_3225_ = lean_ctor_get(v_view_3221_, 3);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_view_3221_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3227_ = v_view_3221_;
v_isShared_3228_ = v_isSharedCheck_3234_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_scopes_3225_);
lean_inc(v_ctx_3224_);
lean_inc(v_imported_3223_);
lean_inc(v_name_3222_);
lean_dec(v_view_3221_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3234_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__3(v_name_3222_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_imported_3223_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_ctx_3224_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_scopes_3225_);
v___x_3231_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_MacroScopesView_review(v___x_3231_);
v___y_3088_ = v___x_3212_;
v___y_3089_ = v___y_3165_;
v___y_3090_ = v___y_3166_;
v___y_3091_ = v___x_3209_;
v___y_3092_ = v___y_3167_;
v___y_3093_ = v___y_3169_;
v___y_3094_ = v___y_3170_;
v___y_3095_ = v___x_3200_;
v___y_3096_ = v___y_3171_;
v___y_3097_ = v___y_3172_;
v___y_3098_ = v___x_3186_;
v___y_3099_ = v___x_3218_;
v___y_3100_ = v___y_3174_;
v___y_3101_ = v___x_3184_;
v___y_3102_ = v___y_3175_;
v___y_3103_ = v___x_3194_;
v___y_3104_ = v___x_3192_;
v___y_3105_ = v___x_3196_;
v___y_3106_ = v___x_3208_;
v___y_3107_ = v___x_3185_;
v___y_3108_ = v___x_3193_;
v___y_3109_ = v___y_3178_;
v___y_3110_ = v___y_3179_;
v___y_3111_ = v___x_3232_;
goto v___jp_3087_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3249_; lean_object* v_a_3250_; lean_object* v_a_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3249_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v___y_3242_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_n(v_a_3250_, 2);
v_a_3251_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3249_);
v___x_3252_ = l_Lean_mkIdentFrom(v_structId_2871_, v___y_3248_, v___x_2887_);
v___x_3253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3253_, 0, v_a_3250_);
lean_ctor_set(v___x_3253_, 1, v___x_2895_);
lean_ctor_set(v___x_3253_, 2, v___x_2896_);
if (lean_obj_tag(v_vis_x3f_2870_) == 1)
{
lean_object* v_val_3254_; lean_object* v___x_3255_; 
v_val_3254_ = lean_ctor_get(v_vis_x3f_2870_, 0);
lean_inc(v_val_3254_);
v___x_3255_ = l_Array_mkArray1___redArg(v_val_3254_);
v___y_3165_ = v___y_3237_;
v___y_3166_ = v___y_3239_;
v___y_3167_ = v___y_3241_;
v___y_3168_ = v___x_3253_;
v___y_3169_ = v___y_3243_;
v___y_3170_ = v___y_3246_;
v___y_3171_ = v_a_3251_;
v___y_3172_ = v___y_3236_;
v___y_3173_ = v___x_3252_;
v___y_3174_ = v___y_3238_;
v___y_3175_ = v___y_3240_;
v___y_3176_ = v_a_3250_;
v___y_3177_ = v___y_3245_;
v___y_3178_ = v___y_3244_;
v___y_3179_ = v___y_3247_;
v___y_3180_ = v___x_3255_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3165_ = v___y_3237_;
v___y_3166_ = v___y_3239_;
v___y_3167_ = v___y_3241_;
v___y_3168_ = v___x_3253_;
v___y_3169_ = v___y_3243_;
v___y_3170_ = v___y_3246_;
v___y_3171_ = v_a_3251_;
v___y_3172_ = v___y_3236_;
v___y_3173_ = v___x_3252_;
v___y_3174_ = v___y_3238_;
v___y_3175_ = v___y_3240_;
v___y_3176_ = v_a_3250_;
v___y_3177_ = v___y_3245_;
v___y_3178_ = v___y_3244_;
v___y_3179_ = v___y_3247_;
v___y_3180_ = v___x_3256_;
goto v___jp_3164_;
}
}
v___jp_3257_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_cmds_3281_; lean_object* v_fields_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3313_; 
v___x_3268_ = l_Array_append___redArg(v___x_2896_, v___y_3267_);
lean_dec_ref(v___y_3267_);
lean_inc_n(v___y_3264_, 5);
v___x_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3269_, 0, v___y_3264_);
lean_ctor_set(v___x_3269_, 1, v___x_2895_);
lean_ctor_set(v___x_3269_, 2, v___x_3268_);
lean_inc_n(v___y_3259_, 9);
lean_inc(v___y_3261_);
v___x_3270_ = l_Lean_Syntax_node7(v___y_3264_, v___y_3261_, v___y_3259_, v___y_3259_, v___x_3269_, v___y_3259_, v___y_3259_, v___y_3259_, v___y_3259_);
v___x_3271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__28));
lean_inc_ref_n(v___y_3266_, 3);
v___x_3272_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3266_, v___x_3271_);
v___x_3273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__29));
v___x_3274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___y_3264_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = ((lean_object*)(l_Lake_configDecl___closed__8));
v___x_3276_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3266_, v___x_3275_);
lean_inc(v___y_3258_);
lean_inc(v___x_3276_);
v___x_3277_ = l_Lean_Syntax_node2(v___y_3264_, v___x_3276_, v___y_3258_, v___y_3259_);
v___x_3278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__30));
v___x_3279_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3266_, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_node2(v___y_3264_, v___x_3279_, v___y_3259_, v___y_3259_);
v_cmds_3281_ = lean_ctor_get(v___y_3260_, 0);
v_fields_3282_ = lean_ctor_get(v___y_3260_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___y_3260_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3284_ = v___y_3260_;
v_isShared_3285_ = v_isSharedCheck_3313_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_fields_3282_);
lean_inc(v_cmds_3281_);
lean_dec(v___y_3260_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3313_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__13));
lean_inc_ref(v___y_3266_);
v___x_3287_ = l_Lean_Name_mkStr4(v___x_2890_, v___x_2891_, v___y_3266_, v___x_3286_);
v___x_3288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
lean_inc(v___y_3264_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 2);
lean_ctor_set(v___x_3284_, 1, v___x_3288_);
lean_ctor_set(v___x_3284_, 0, v___y_3264_);
v___x_3290_ = v___x_3284_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___y_3264_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3291_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__55));
lean_inc_n(v___y_3259_, 3);
lean_inc_n(v___y_3264_, 3);
v___x_3292_ = l_Lean_Syntax_node2(v___y_3264_, v___x_3291_, v___y_3259_, v___y_3259_);
lean_inc(v___x_3287_);
v___x_3293_ = l_Lean_Syntax_node4(v___y_3264_, v___x_3287_, v___x_3290_, v_fields_3282_, v___x_3292_, v___y_3259_);
v___x_3294_ = l_Lean_Syntax_node5(v___y_3264_, v___x_3272_, v___x_3274_, v___x_3277_, v___x_3280_, v___x_3293_, v___y_3259_);
lean_inc(v___y_3262_);
v___x_3295_ = l_Lean_Syntax_node2(v___y_3264_, v___y_3262_, v___x_3270_, v___x_3294_);
v___x_3296_ = l_Lean_Name_hasMacroScopes(v___y_3265_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
lean_inc(v___y_3265_);
v___x_3297_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v___y_3265_);
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___x_3291_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v_cmds_3281_;
v___y_3240_ = v___x_3295_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3263_;
v___y_3243_ = v___y_3265_;
v___y_3244_ = v___x_3276_;
v___y_3245_ = v___y_3266_;
v___y_3246_ = v___x_3288_;
v___y_3247_ = v___x_3287_;
v___y_3248_ = v___x_3297_;
goto v___jp_3235_;
}
else
{
lean_object* v_view_3298_; lean_object* v_name_3299_; lean_object* v_imported_3300_; lean_object* v_ctx_3301_; lean_object* v_scopes_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3311_; 
lean_inc(v___y_3265_);
v_view_3298_ = l_Lean_extractMacroScopes(v___y_3265_);
v_name_3299_ = lean_ctor_get(v_view_3298_, 0);
v_imported_3300_ = lean_ctor_get(v_view_3298_, 1);
v_ctx_3301_ = lean_ctor_get(v_view_3298_, 2);
v_scopes_3302_ = lean_ctor_get(v_view_3298_, 3);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_view_3298_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3304_ = v_view_3298_;
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_scopes_3302_);
lean_inc(v_ctx_3301_);
lean_inc(v_imported_3300_);
lean_inc(v_name_3299_);
lean_dec(v_view_3298_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__2(v_name_3299_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_imported_3300_);
lean_ctor_set(v_reuseFailAlloc_3310_, 2, v_ctx_3301_);
lean_ctor_set(v_reuseFailAlloc_3310_, 3, v_scopes_3302_);
v___x_3308_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_MacroScopesView_review(v___x_3308_);
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___x_3291_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v_cmds_3281_;
v___y_3240_ = v___x_3295_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3263_;
v___y_3243_ = v___y_3265_;
v___y_3244_ = v___x_3276_;
v___y_3245_ = v___y_3266_;
v___y_3246_ = v___x_3288_;
v___y_3247_ = v___x_3287_;
v___y_3248_ = v___x_3309_;
goto v___jp_3235_;
}
}
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3319_; lean_object* v_a_3320_; lean_object* v_a_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3319_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__0(v_ref_2879_, v_a_2875_, v___y_3317_);
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc_n(v_a_3320_, 2);
v_a_3321_ = lean_ctor_get(v___x_3319_, 1);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3319_);
v___x_3322_ = l_Lean_mkIdentFrom(v_structId_2871_, v___y_3318_, v___x_2887_);
v___x_3323_ = ((lean_object*)(l_Lake_configDecl___closed__31));
v___x_3324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_3325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3326_, 0, v_a_3320_);
lean_ctor_set(v___x_3326_, 1, v___x_2895_);
lean_ctor_set(v___x_3326_, 2, v___x_2896_);
if (lean_obj_tag(v_vis_x3f_2870_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
v_val_3327_ = lean_ctor_get(v_vis_x3f_2870_, 0);
lean_inc(v_val_3327_);
v___x_3328_ = l_Array_mkArray1___redArg(v_val_3327_);
v___y_3258_ = v___x_3322_;
v___y_3259_ = v___x_3326_;
v___y_3260_ = v___y_3315_;
v___y_3261_ = v___x_3325_;
v___y_3262_ = v___x_3324_;
v___y_3263_ = v_a_3321_;
v___y_3264_ = v_a_3320_;
v___y_3265_ = v___y_3316_;
v___y_3266_ = v___x_3323_;
v___y_3267_ = v___x_3328_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3329_; 
v___x_3329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_3258_ = v___x_3322_;
v___y_3259_ = v___x_3326_;
v___y_3260_ = v___y_3315_;
v___y_3261_ = v___x_3325_;
v___y_3262_ = v___x_3324_;
v___y_3263_ = v_a_3321_;
v___y_3264_ = v_a_3320_;
v___y_3265_ = v___y_3316_;
v___y_3266_ = v___x_3323_;
v___y_3267_ = v___x_3329_;
goto v___jp_3257_;
}
}
v___jp_3330_:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = l_Lean_TSyntax_getId(v_structId_2871_);
v___x_3334_ = l_Lean_Name_hasMacroScopes(v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_inc(v___x_3333_);
v___x_3335_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v___x_3333_);
v___y_3315_ = v_a_3331_;
v___y_3316_ = v___x_3333_;
v___y_3317_ = v_a_3332_;
v___y_3318_ = v___x_3335_;
goto v___jp_3314_;
}
else
{
lean_object* v_view_3336_; lean_object* v_name_3337_; lean_object* v_imported_3338_; lean_object* v_ctx_3339_; lean_object* v_scopes_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3349_; 
lean_inc(v___x_3333_);
v_view_3336_ = l_Lean_extractMacroScopes(v___x_3333_);
v_name_3337_ = lean_ctor_get(v_view_3336_, 0);
v_imported_3338_ = lean_ctor_get(v_view_3336_, 1);
v_ctx_3339_ = lean_ctor_get(v_view_3336_, 2);
v_scopes_3340_ = lean_ctor_get(v_view_3336_, 3);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_view_3336_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3342_ = v_view_3336_;
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_scopes_3340_);
lean_inc(v_ctx_3339_);
lean_inc(v_imported_3338_);
lean_inc(v_name_3337_);
lean_dec(v_view_3336_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___lam__1(v_name_3337_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3344_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_imported_3338_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_ctx_3339_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_scopes_3340_);
v___x_3346_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_MacroScopesView_review(v___x_3346_);
v___y_3315_ = v_a_3331_;
v___y_3316_ = v___x_3333_;
v___y_3317_ = v_a_3332_;
v___y_3318_ = v___x_3347_;
goto v___jp_3314_;
}
}
}
}
v___jp_3350_:
{
if (lean_obj_tag(v___y_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v_a_3353_; 
v_a_3352_ = lean_ctor_get(v___y_3351_, 0);
lean_inc(v_a_3352_);
v_a_3353_ = lean_ctor_get(v___y_3351_, 1);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___y_3351_, 2);
v_a_3331_ = v_a_3352_;
v_a_3332_ = v_a_3353_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3354_; lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_del_object(v___x_2884_);
lean_dec(v_structTy_2873_);
lean_dec(v_structArity_2872_);
lean_dec(v_structId_2871_);
lean_dec(v_vis_x3f_2870_);
v_a_3354_ = lean_ctor_get(v___y_3351_, 0);
v_a_3355_ = lean_ctor_get(v___y_3351_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___y_3351_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___y_3351_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_inc(v_a_3354_);
lean_dec(v___y_3351_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3354_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___boxed(lean_object* v_vis_x3f_3373_, lean_object* v_structId_3374_, lean_object* v_structArity_3375_, lean_object* v_structTy_3376_, lean_object* v_views_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v_vis_x3f_3373_, v_structId_3374_, v_structArity_3375_, v_structTy_3376_, v_views_3377_, v_a_3378_, v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3380_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(size_t v_sz_3381_, size_t v_i_3382_, lean_object* v_bs_3383_){
_start:
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_usize_dec_lt(v_i_3382_, v_sz_3381_);
if (v___x_3384_ == 0)
{
return v_bs_3383_;
}
else
{
lean_object* v_v_3385_; lean_object* v_id_3386_; lean_object* v___x_3387_; lean_object* v_bs_x27_3388_; size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v_v_3385_ = lean_array_uget_borrowed(v_bs_3383_, v_i_3382_);
v_id_3386_ = lean_ctor_get(v_v_3385_, 1);
lean_inc(v_id_3386_);
v___x_3387_ = lean_unsigned_to_nat(0u);
v_bs_x27_3388_ = lean_array_uset(v_bs_3383_, v_i_3382_, v___x_3387_);
v___x_3389_ = ((size_t)1ULL);
v___x_3390_ = lean_usize_add(v_i_3382_, v___x_3389_);
v___x_3391_ = lean_array_uset(v_bs_x27_3388_, v_i_3382_, v_id_3386_);
v_i_3382_ = v___x_3390_;
v_bs_3383_ = v___x_3391_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3381_ = stack[0].m_num;
size_t v_i_3382_ = stack[1].m_num;
lean_object* v_bs_3383_ = stack[2].m_obj;
lean_object* v_res_3393_;
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_3381_, v_i_3382_, v_bs_3383_);
stack->m_obj
 = v_res_3393_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0___boxed(lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_bs_3396_){
_start:
{
size_t v_sz_boxed_3397_; size_t v_i_boxed_3398_; lean_object* v_res_3399_; 
v_sz_boxed_3397_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_boxed_3397_, v_i_boxed_3398_, v_bs_3396_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView(lean_object* v_stx_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_methods_3423_; lean_object* v_quotContext_3424_; lean_object* v_currMacroScope_3425_; lean_object* v_currRecDepth_3426_; lean_object* v_maxRecDepth_3427_; lean_object* v_ref_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v_ref_3431_; lean_object* v___x_3432_; 
v_methods_3423_ = lean_ctor_get(v_a_3421_, 0);
v_quotContext_3424_ = lean_ctor_get(v_a_3421_, 1);
v_currMacroScope_3425_ = lean_ctor_get(v_a_3421_, 2);
v_currRecDepth_3426_ = lean_ctor_get(v_a_3421_, 3);
v_maxRecDepth_3427_ = lean_ctor_get(v_a_3421_, 4);
v_ref_3428_ = lean_ctor_get(v_a_3421_, 5);
v___x_3429_ = ((lean_object*)(l_Lake_configField___closed__2));
lean_inc(v_stx_3420_);
v___x_3430_ = l_Lean_Syntax_isOfKind(v_stx_3420_, v___x_3429_);
v_ref_3431_ = l_Lean_replaceRef(v_stx_3420_, v_ref_3428_);
lean_inc(v_maxRecDepth_3427_);
lean_inc(v_currRecDepth_3426_);
lean_inc(v_currMacroScope_3425_);
lean_inc(v_quotContext_3424_);
lean_inc(v_methods_3423_);
v___x_3432_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3432_, 0, v_methods_3423_);
lean_ctor_set(v___x_3432_, 1, v_quotContext_3424_);
lean_ctor_set(v___x_3432_, 2, v_currMacroScope_3425_);
lean_ctor_set(v___x_3432_, 3, v_currRecDepth_3426_);
lean_ctor_set(v___x_3432_, 4, v_maxRecDepth_3427_);
lean_ctor_set(v___x_3432_, 5, v_ref_3431_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_stx_3420_);
v___x_3433_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3434_ = l_Lean_Macro_throwError___redArg(v___x_3433_, v___x_3432_, v_a_3422_);
lean_dec_ref_known(v___x_3432_, 6);
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v_mods_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v_val_3448_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_val_x3f_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v_mods_3436_ = l_Lean_Syntax_getArg(v_stx_3420_, v___x_3435_);
v___x_3437_ = ((lean_object*)(l_Lake_configDecl___closed__24));
v___x_3438_ = ((lean_object*)(l_Lake_configDecl___closed__25));
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v_mods_3436_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v_mods_3436_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3543_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3544_ = l_Lean_Macro_throwError___redArg(v___x_3543_, v___x_3432_, v_a_3422_);
lean_dec_ref_known(v___x_3432_, 6);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; lean_object* v_id_x3f_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3575_ = l_Lean_Syntax_getArg(v_stx_3420_, v___x_3545_);
v___x_3576_ = l_Lean_Syntax_isNone(v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3577_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3575_);
v___x_3578_ = l_Lean_Syntax_matchesNull(v___x_3575_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec(v___x_3575_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3579_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3580_ = l_Lean_Macro_throwError___redArg(v___x_3579_, v___x_3432_, v_a_3422_);
lean_dec_ref_known(v___x_3432_, 6);
return v___x_3580_;
}
else
{
lean_object* v_id_x3f_3581_; lean_object* v___x_3582_; 
v_id_x3f_3581_ = l_Lean_Syntax_getArg(v___x_3575_, v___x_3435_);
lean_dec(v___x_3575_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_id_x3f_3581_);
v_id_x3f_3547_ = v___x_3582_;
v___y_3548_ = v___x_3432_;
v___y_3549_ = v_a_3422_;
goto v___jp_3546_;
}
}
else
{
lean_object* v___x_3583_; 
lean_dec(v___x_3575_);
v___x_3583_ = lean_box(0);
v_id_x3f_3547_ = v___x_3583_;
v___y_3548_ = v___x_3432_;
v___y_3549_ = v_a_3422_;
goto v___jp_3546_;
}
v___jp_3546_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3550_ = lean_unsigned_to_nat(3u);
v___x_3551_ = l_Lean_Syntax_getArg(v_stx_3420_, v___x_3550_);
v___x_3552_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__7));
lean_inc(v___x_3551_);
v___x_3553_ = l_Lean_Syntax_isOfKind(v___x_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec(v___x_3551_);
lean_dec(v_id_x3f_3547_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3554_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3555_ = l_Lean_Macro_throwError___redArg(v___x_3554_, v___y_3548_, v___y_3549_);
lean_dec_ref(v___y_3548_);
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3556_ = l_Lean_Syntax_getArg(v___x_3551_, v___x_3545_);
v___x_3557_ = ((lean_object*)(l_Lake_configDecl___closed__26));
v___x_3558_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__45));
lean_inc(v___x_3556_);
v___x_3559_ = l_Lean_Syntax_isOfKind(v___x_3556_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v___x_3556_);
lean_dec(v___x_3551_);
lean_dec(v_id_x3f_3547_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3560_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3561_ = l_Lean_Macro_throwError___redArg(v___x_3560_, v___y_3548_, v___y_3549_);
lean_dec_ref(v___y_3548_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_rty_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3562_ = lean_unsigned_to_nat(2u);
v___x_3563_ = l_Lean_Syntax_getArg(v_stx_3420_, v___x_3562_);
v___x_3564_ = l_Lean_Syntax_getArg(v___x_3551_, v___x_3435_);
lean_dec(v___x_3551_);
v_rty_3565_ = l_Lean_Syntax_getArg(v___x_3556_, v___x_3545_);
lean_dec(v___x_3556_);
v___x_3566_ = lean_unsigned_to_nat(4u);
v___x_3567_ = l_Lean_Syntax_getArg(v_stx_3420_, v___x_3566_);
v___x_3568_ = l_Lean_Syntax_isNone(v___x_3567_);
if (v___x_3568_ == 0)
{
uint8_t v___x_3569_; 
lean_inc(v___x_3567_);
v___x_3569_ = l_Lean_Syntax_matchesNull(v___x_3567_, v___x_3562_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec(v___x_3567_);
lean_dec(v_rty_3565_);
lean_dec(v___x_3564_);
lean_dec(v___x_3563_);
lean_dec(v_id_x3f_3547_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3570_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__0));
v___x_3571_ = l_Lean_Macro_throwError___redArg(v___x_3570_, v___y_3548_, v___y_3549_);
lean_dec_ref(v___y_3548_);
return v___x_3571_;
}
else
{
lean_object* v_val_x3f_3572_; lean_object* v___x_3573_; 
v_val_x3f_3572_ = l_Lean_Syntax_getArg(v___x_3567_, v___x_3545_);
lean_dec(v___x_3567_);
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_val_x3f_3572_);
v___y_3510_ = v___x_3564_;
v___y_3511_ = v___x_3563_;
v___y_3512_ = v___x_3558_;
v___y_3513_ = v_rty_3565_;
v___y_3514_ = v_id_x3f_3547_;
v___y_3515_ = v___x_3557_;
v_val_x3f_3516_ = v___x_3573_;
v___y_3517_ = v___y_3548_;
v___y_3518_ = v___y_3549_;
goto v___jp_3509_;
}
}
else
{
lean_object* v___x_3574_; 
lean_dec(v___x_3567_);
v___x_3574_ = lean_box(0);
v___y_3510_ = v___x_3564_;
v___y_3511_ = v___x_3563_;
v___y_3512_ = v___x_3558_;
v___y_3513_ = v_rty_3565_;
v___y_3514_ = v_id_x3f_3547_;
v___y_3515_ = v___x_3557_;
v_val_x3f_3516_ = v___x_3574_;
v___y_3517_ = v___y_3548_;
v___y_3518_ = v___y_3549_;
goto v___jp_3509_;
}
}
}
}
}
v___jp_3439_:
{
lean_object* v_methods_3449_; lean_object* v_quotContext_3450_; lean_object* v_currMacroScope_3451_; lean_object* v_currRecDepth_3452_; lean_object* v_maxRecDepth_3453_; lean_object* v_ref_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3508_; 
v_methods_3449_ = lean_ctor_get(v___y_3443_, 0);
v_quotContext_3450_ = lean_ctor_get(v___y_3443_, 1);
v_currMacroScope_3451_ = lean_ctor_get(v___y_3443_, 2);
v_currRecDepth_3452_ = lean_ctor_get(v___y_3443_, 3);
v_maxRecDepth_3453_ = lean_ctor_get(v___y_3443_, 4);
v_ref_3454_ = lean_ctor_get(v___y_3443_, 5);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___y_3443_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3456_ = v___y_3443_;
v_isShared_3457_ = v_isSharedCheck_3508_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_ref_3454_);
lean_inc(v_maxRecDepth_3453_);
lean_inc(v_currRecDepth_3452_);
lean_inc(v_currMacroScope_3451_);
lean_inc(v_quotContext_3450_);
lean_inc(v_methods_3449_);
lean_dec(v___y_3443_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3508_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_ref_3458_; 
v_ref_3458_ = l_Lean_replaceRef(v_val_3448_, v_ref_3454_);
lean_dec(v_ref_3454_);
if (lean_obj_tag(v___y_3440_) == 1)
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3502_; 
lean_del_object(v___x_3456_);
lean_dec(v_maxRecDepth_3453_);
lean_dec(v_currRecDepth_3452_);
lean_dec(v_currMacroScope_3451_);
lean_dec(v_quotContext_3450_);
lean_dec(v_methods_3449_);
v_val_3459_ = lean_ctor_get(v___y_3440_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___y_3440_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3461_ = v___y_3440_;
v_isShared_3462_ = v_isSharedCheck_3502_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v___y_3440_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3502_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; size_t v_sz_3472_; size_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3463_ = 0;
v___x_3464_ = l_Lean_SourceInfo_fromRef(v_ref_3458_, v___x_3463_);
lean_dec(v_ref_3458_);
v___x_3465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__75));
lean_inc_ref_n(v___y_3447_, 3);
v___x_3466_ = l_Lean_Name_mkStr4(v___x_3437_, v___x_3438_, v___y_3447_, v___x_3465_);
lean_inc_n(v___x_3464_, 13);
v___x_3467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3464_);
lean_ctor_set(v___x_3467_, 1, v___x_3465_);
v___x_3468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__76));
v___x_3469_ = l_Lean_Name_mkStr4(v___x_3437_, v___x_3438_, v___y_3447_, v___x_3468_);
v___x_3470_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_3471_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_3472_ = lean_array_size(v___y_3444_);
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Meta_0__Lake_mkFieldView_spec__0(v_sz_3472_, v___x_3473_, v___y_3444_);
v___x_3475_ = l_Array_append___redArg(v___x_3471_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3464_);
lean_ctor_set(v___x_3476_, 1, v___x_3470_);
lean_ctor_set(v___x_3476_, 2, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3464_);
lean_ctor_set(v___x_3477_, 1, v___x_3470_);
lean_ctor_set(v___x_3477_, 2, v___x_3471_);
v___x_3478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__77));
v___x_3479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3464_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
lean_inc_ref(v___x_3477_);
v___x_3480_ = l_Lean_Syntax_node4(v___x_3464_, v___x_3469_, v___x_3476_, v___x_3477_, v___x_3479_, v_val_3459_);
v___x_3481_ = l_Lean_Syntax_node2(v___x_3464_, v___x_3466_, v___x_3467_, v___x_3480_);
v___x_3482_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__2));
v___x_3483_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_3484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__3));
v___x_3485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3464_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
lean_inc(v___y_3446_);
lean_inc(v___y_3442_);
v___x_3486_ = l_Lean_Syntax_node2(v___x_3464_, v___y_3442_, v___x_3485_, v___y_3446_);
v___x_3487_ = l_Lean_Syntax_node1(v___x_3464_, v___x_3470_, v___x_3486_);
v___x_3488_ = l_Lean_Syntax_node2(v___x_3464_, v___x_3483_, v___x_3477_, v___x_3487_);
v___x_3489_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__4));
v___x_3490_ = l_Lean_Name_mkStr4(v___x_3437_, v___x_3438_, v___y_3447_, v___x_3489_);
v___x_3491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__14));
v___x_3492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3464_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
lean_inc(v___x_3481_);
v___x_3493_ = l_Lean_Syntax_node2(v___x_3464_, v___x_3490_, v___x_3492_, v___x_3481_);
v___x_3494_ = l_Lean_Syntax_node1(v___x_3464_, v___x_3470_, v___x_3493_);
lean_inc(v_val_3448_);
lean_inc(v_mods_3436_);
v___x_3495_ = l_Lean_Syntax_node4(v___x_3464_, v___x_3482_, v_mods_3436_, v_val_3448_, v___x_3488_, v___x_3494_);
v___x_3496_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_3441_);
lean_dec_ref(v___y_3441_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3495_);
v___x_3498_ = v___x_3461_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3495_);
v___x_3498_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3499_, 0, v_stx_3420_);
lean_ctor_set(v___x_3499_, 1, v_mods_3436_);
lean_ctor_set(v___x_3499_, 2, v_val_3448_);
lean_ctor_set(v___x_3499_, 3, v___x_3496_);
lean_ctor_set(v___x_3499_, 4, v___y_3446_);
lean_ctor_set(v___x_3499_, 5, v___x_3481_);
lean_ctor_set(v___x_3499_, 6, v___x_3498_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*7, v___x_3463_);
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___y_3445_);
return v___x_3500_;
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec(v_val_3448_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 5, v_ref_3458_);
v___x_3504_ = v___x_3456_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_methods_3449_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_quotContext_3450_);
lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_currMacroScope_3451_);
lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_currRecDepth_3452_);
lean_ctor_set(v_reuseFailAlloc_3507_, 4, v_maxRecDepth_3453_);
lean_ctor_set(v_reuseFailAlloc_3507_, 5, v_ref_3458_);
v___x_3504_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__5));
v___x_3506_ = l_Lean_Macro_throwError___redArg(v___x_3505_, v___x_3504_, v___y_3445_);
lean_dec_ref(v___x_3504_);
return v___x_3506_;
}
}
}
}
v___jp_3509_:
{
lean_object* v_bs_3519_; lean_object* v___x_3520_; 
v_bs_3519_ = l_Lean_Syntax_getArgs(v___y_3510_);
lean_dec(v___y_3510_);
v___x_3520_ = l_Lake_expandBinders(v_bs_3519_, v___y_3517_, v___y_3518_);
lean_dec_ref(v_bs_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_a_3522_; lean_object* v_ids_3523_; lean_object* v___x_3524_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
v_a_3522_ = lean_ctor_get(v___x_3520_, 1);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3520_, 2);
v_ids_3523_ = l_Lean_Syntax_getArgs(v___y_3511_);
lean_dec(v___y_3511_);
v___x_3524_ = l_Lake_mkDepArrow(v_a_3521_, v___y_3513_);
if (lean_obj_tag(v___y_3514_) == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3525_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3523_);
v___x_3526_ = lean_array_get_size(v___x_3525_);
v___x_3527_ = lean_nat_dec_lt(v___x_3435_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec_ref(v___x_3525_);
lean_dec(v___x_3524_);
lean_dec_ref(v_ids_3523_);
lean_dec(v_a_3521_);
lean_dec(v_val_x3f_3516_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v___x_3528_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__6));
v___x_3529_ = l_Lean_Macro_throwError___redArg(v___x_3528_, v___y_3517_, v_a_3522_);
lean_dec_ref(v___y_3517_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_array_fget(v___x_3525_, v___x_3435_);
lean_dec_ref(v___x_3525_);
v___y_3440_ = v_val_x3f_3516_;
v___y_3441_ = v_ids_3523_;
v___y_3442_ = v___y_3512_;
v___y_3443_ = v___y_3517_;
v___y_3444_ = v_a_3521_;
v___y_3445_ = v_a_3522_;
v___y_3446_ = v___x_3524_;
v___y_3447_ = v___y_3515_;
v_val_3448_ = v___x_3530_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_val_3531_; 
v_val_3531_ = lean_ctor_get(v___y_3514_, 0);
lean_inc(v_val_3531_);
lean_dec_ref_known(v___y_3514_, 1);
v___y_3440_ = v_val_x3f_3516_;
v___y_3441_ = v_ids_3523_;
v___y_3442_ = v___y_3512_;
v___y_3443_ = v___y_3517_;
v___y_3444_ = v_a_3521_;
v___y_3445_ = v_a_3522_;
v___y_3446_ = v___x_3524_;
v___y_3447_ = v___y_3515_;
v_val_3448_ = v_val_3531_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v___y_3517_);
lean_dec(v_val_x3f_3516_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec(v___y_3511_);
lean_dec(v_mods_3436_);
lean_dec(v_stx_3420_);
v_a_3532_ = lean_ctor_get(v___x_3520_, 0);
v_a_3533_ = lean_ctor_get(v___x_3520_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3520_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
lean_dec(v___x_3520_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3532_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkFieldView___boxed(lean_object* v_stx_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_stx_3584_, v_a_3585_, v_a_3586_);
lean_dec_ref(v_a_3585_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(lean_object* v_typeName_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3590_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___closed__0));
v___x_3591_ = l_Lean_Name_getString_x21(v_typeName_3589_);
v___x_3592_ = lean_string_append(v___x_3590_, v___x_3591_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = lean_box(0);
v___x_3594_ = l_Lean_Name_str___override(v___x_3593_, v___x_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0___boxed(lean_object* v_typeName_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_typeName_3595_);
lean_dec(v_typeName_3595_);
return v_res_3596_;
}
}
static lean_object* _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3607_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__6);
v___x_3608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
v___x_3609_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__0);
v___x_3610_ = l_Lean_Syntax_node7(v___x_3609_, v___x_3608_, v___x_3607_, v___x_3607_, v___x_3607_, v___x_3607_, v___x_3607_, v___x_3607_, v___x_3607_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(lean_object* v_stx_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_methods_3616_; lean_object* v_quotContext_3617_; lean_object* v_currMacroScope_3618_; lean_object* v_currRecDepth_3619_; lean_object* v_maxRecDepth_3620_; lean_object* v_ref_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v_id_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v_ref_3652_; lean_object* v___x_3653_; 
v_methods_3616_ = lean_ctor_get(v_a_3614_, 0);
v_quotContext_3617_ = lean_ctor_get(v_a_3614_, 1);
v_currMacroScope_3618_ = lean_ctor_get(v_a_3614_, 2);
v_currRecDepth_3619_ = lean_ctor_get(v_a_3614_, 3);
v_maxRecDepth_3620_ = lean_ctor_get(v_a_3614_, 4);
v_ref_3621_ = lean_ctor_get(v_a_3614_, 5);
v___x_3622_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__1));
lean_inc(v_stx_3613_);
v___x_3623_ = l_Lean_Syntax_isOfKind(v_stx_3613_, v___x_3622_);
v_ref_3652_ = l_Lean_replaceRef(v_stx_3613_, v_ref_3621_);
lean_inc(v_maxRecDepth_3620_);
lean_inc(v_currRecDepth_3619_);
lean_inc(v_currMacroScope_3618_);
lean_inc(v_quotContext_3617_);
lean_inc(v_methods_3616_);
v___x_3653_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3653_, 0, v_methods_3616_);
lean_ctor_set(v___x_3653_, 1, v_quotContext_3617_);
lean_ctor_set(v___x_3653_, 2, v_currMacroScope_3618_);
lean_ctor_set(v___x_3653_, 3, v_currRecDepth_3619_);
lean_ctor_set(v___x_3653_, 4, v_maxRecDepth_3620_);
lean_ctor_set(v___x_3653_, 5, v_ref_3652_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_stx_3613_);
v___x_3654_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3655_ = l_Lean_Macro_throwError___redArg(v___x_3654_, v___x_3653_, v_a_3615_);
lean_dec_ref_known(v___x_3653_, 6);
return v___x_3655_;
}
else
{
lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v_typeId_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___x_3679_; lean_object* v_id_x3f_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3719_ = l_Lean_Syntax_getArg(v_stx_3613_, v___x_3679_);
v___x_3720_ = l_Lean_Syntax_isNone(v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; uint8_t v___x_3722_; 
v___x_3721_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3719_);
v___x_3722_ = l_Lean_Syntax_matchesNull(v___x_3719_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v___x_3719_);
lean_dec(v_stx_3613_);
v___x_3723_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__6));
v___x_3724_ = l_Lean_Macro_throwError___redArg(v___x_3723_, v___x_3653_, v_a_3615_);
lean_dec_ref_known(v___x_3653_, 6);
return v___x_3724_;
}
else
{
lean_object* v_id_x3f_3725_; lean_object* v___x_3726_; 
v_id_x3f_3725_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3679_);
lean_dec(v___x_3719_);
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_id_x3f_3725_);
v_id_x3f_3681_ = v___x_3726_;
v___y_3682_ = v___x_3653_;
v___y_3683_ = v_a_3615_;
goto v___jp_3680_;
}
}
else
{
lean_object* v___x_3727_; 
lean_dec(v___x_3719_);
v___x_3727_ = lean_box(0);
v_id_x3f_3681_ = v___x_3727_;
v___y_3682_ = v___x_3653_;
v___y_3683_ = v_a_3615_;
goto v___jp_3680_;
}
v___jp_3656_:
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = l_Lean_TSyntax_getId(v_typeId_3659_);
v___x_3663_ = l_Lean_Name_hasMacroScopes(v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v___x_3662_);
lean_dec(v___x_3662_);
v___y_3644_ = v___y_3661_;
v___y_3645_ = v___y_3657_;
v___y_3646_ = v___y_3660_;
v___y_3647_ = v___y_3658_;
v___y_3648_ = v_typeId_3659_;
v___y_3649_ = v___x_3664_;
goto v___jp_3643_;
}
else
{
lean_object* v_view_3665_; lean_object* v_name_3666_; lean_object* v_imported_3667_; lean_object* v_ctx_3668_; lean_object* v_scopes_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3678_; 
v_view_3665_ = l_Lean_extractMacroScopes(v___x_3662_);
v_name_3666_ = lean_ctor_get(v_view_3665_, 0);
v_imported_3667_ = lean_ctor_get(v_view_3665_, 1);
v_ctx_3668_ = lean_ctor_get(v_view_3665_, 2);
v_scopes_3669_ = lean_ctor_get(v_view_3665_, 3);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_view_3665_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3671_ = v_view_3665_;
v_isShared_3672_ = v_isSharedCheck_3678_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_scopes_3669_);
lean_inc(v_ctx_3668_);
lean_inc(v_imported_3667_);
lean_inc(v_name_3666_);
lean_dec(v_view_3665_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3678_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___lam__0(v_name_3666_);
lean_dec(v_name_3666_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3673_);
v___x_3675_ = v___x_3671_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_imported_3667_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_ctx_3668_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v_scopes_3669_);
v___x_3675_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_MacroScopesView_review(v___x_3675_);
v___y_3644_ = v___y_3661_;
v___y_3645_ = v___y_3657_;
v___y_3646_ = v___y_3660_;
v___y_3647_ = v___y_3658_;
v___y_3648_ = v_typeId_3659_;
v___y_3649_ = v___x_3676_;
goto v___jp_3643_;
}
}
}
}
v___jp_3680_:
{
lean_object* v___x_3684_; lean_object* v_id_3685_; 
v___x_3684_ = lean_unsigned_to_nat(1u);
v_id_3685_ = l_Lean_Syntax_getArg(v_stx_3613_, v___x_3684_);
if (lean_obj_tag(v_id_x3f_3681_) == 1)
{
lean_object* v_val_3686_; 
v_val_3686_ = lean_ctor_get(v_id_x3f_3681_, 0);
lean_inc(v_val_3686_);
lean_dec_ref_known(v_id_x3f_3681_, 1);
v___y_3625_ = v_id_3685_;
v___y_3626_ = v___x_3684_;
v_id_3627_ = v_val_3686_;
v___y_3628_ = v___y_3682_;
v___y_3629_ = v___y_3683_;
goto v___jp_3624_;
}
else
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
lean_dec(v_id_x3f_3681_);
v___x_3687_ = ((lean_object*)(l_Lake_configField___closed__13));
lean_inc(v_id_3685_);
v___x_3688_ = l_Lean_Syntax_isOfKind(v_id_3685_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__46));
lean_inc(v_id_3685_);
v___x_3690_ = l_Lean_Syntax_isOfKind(v_id_3685_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3692_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3685_, v___x_3691_, v___y_3682_, v___y_3683_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_a_3694_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
v_a_3694_ = lean_ctor_get(v___x_3692_, 1);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3692_, 2);
v___y_3657_ = v_id_3685_;
v___y_3658_ = v___x_3684_;
v_typeId_3659_ = v_a_3693_;
v___y_3660_ = v___y_3682_;
v___y_3661_ = v_a_3694_;
goto v___jp_3656_;
}
else
{
lean_object* v_a_3695_; lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_id_3685_);
lean_dec_ref(v___y_3682_);
lean_dec(v_stx_3613_);
v_a_3695_ = lean_ctor_get(v___x_3692_, 0);
v_a_3696_ = lean_ctor_get(v___x_3692_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3692_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_inc(v_a_3695_);
lean_dec(v___x_3692_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3695_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_id_3704_; uint8_t v___x_3705_; 
v_id_3704_ = l_Lean_Syntax_getArg(v_id_3685_, v___x_3679_);
lean_inc(v_id_3704_);
v___x_3705_ = l_Lean_Syntax_isOfKind(v_id_3704_, v___x_3687_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_dec(v_id_3704_);
v___x_3706_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__7));
v___x_3707_ = l_Lean_Macro_throwErrorAt___redArg(v_id_3685_, v___x_3706_, v___y_3682_, v___y_3683_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v_a_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
v_a_3709_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3707_, 2);
v___y_3657_ = v_id_3685_;
v___y_3658_ = v___x_3684_;
v_typeId_3659_ = v_a_3708_;
v___y_3660_ = v___y_3682_;
v___y_3661_ = v_a_3709_;
goto v___jp_3656_;
}
else
{
lean_object* v_a_3710_; lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_id_3685_);
lean_dec_ref(v___y_3682_);
lean_dec(v_stx_3613_);
v_a_3710_ = lean_ctor_get(v___x_3707_, 0);
v_a_3711_ = lean_ctor_get(v___x_3707_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3707_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_inc(v_a_3710_);
lean_dec(v___x_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3710_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
else
{
v___y_3657_ = v_id_3685_;
v___y_3658_ = v___x_3684_;
v_typeId_3659_ = v_id_3704_;
v___y_3660_ = v___y_3682_;
v___y_3661_ = v___y_3683_;
goto v___jp_3656_;
}
}
}
else
{
lean_inc(v_id_3685_);
v___y_3657_ = v_id_3685_;
v___y_3658_ = v___x_3684_;
v_typeId_3659_ = v_id_3685_;
v___y_3660_ = v___y_3682_;
v___y_3661_ = v___y_3683_;
goto v___jp_3656_;
}
}
}
}
v___jp_3624_:
{
lean_object* v_ref_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_ref_3630_ = lean_ctor_get(v___y_3628_, 5);
lean_inc(v_ref_3630_);
lean_dec_ref(v___y_3628_);
v___x_3631_ = 0;
v___x_3632_ = l_Lean_SourceInfo_fromRef(v_ref_3630_, v___x_3631_);
lean_dec(v_ref_3630_);
v___x_3633_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__3));
v___x_3634_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__4));
lean_inc(v___x_3632_);
v___x_3635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3632_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_Syntax_node1(v___x_3632_, v___x_3633_, v___x_3635_);
v___x_3637_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5, &l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___closed__5);
v___x_3638_ = lean_mk_empty_array_with_capacity(v___y_3626_);
lean_inc(v_id_3627_);
v___x_3639_ = lean_array_push(v___x_3638_, v_id_3627_);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3641_, 0, v_stx_3613_);
lean_ctor_set(v___x_3641_, 1, v___x_3637_);
lean_ctor_set(v___x_3641_, 2, v_id_3627_);
lean_ctor_set(v___x_3641_, 3, v___x_3639_);
lean_ctor_set(v___x_3641_, 4, v___y_3625_);
lean_ctor_set(v___x_3641_, 5, v___x_3636_);
lean_ctor_set(v___x_3641_, 6, v___x_3640_);
lean_ctor_set_uint8(v___x_3641_, sizeof(void*)*7, v___x_3623_);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___y_3629_);
return v___x_3642_;
}
v___jp_3643_:
{
uint8_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = 0;
v___x_3651_ = l_Lean_mkIdentFrom(v___y_3648_, v___y_3649_, v___x_3650_);
lean_dec(v___y_3648_);
v___y_3625_ = v___y_3645_;
v___y_3626_ = v___y_3647_;
v_id_3627_ = v___x_3651_;
v___y_3628_ = v___y_3646_;
v___y_3629_ = v___y_3644_;
goto v___jp_3624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Meta_0__Lake_mkParentFieldView___boxed(lean_object* v_stx_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v_stx_3728_, v_a_3729_, v_a_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__0(lean_object* v_x_3732_){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___x_3734_ = lean_array_push(v___x_3733_, v_x_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___lam__1(lean_object* v_00___3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
return v___x_3736_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(size_t v_sz_3737_, size_t v_i_3738_, lean_object* v_bs_3739_){
_start:
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_usize_dec_lt(v_i_3738_, v_sz_3737_);
if (v___x_3740_ == 0)
{
return v_bs_3739_;
}
else
{
lean_object* v_v_3741_; lean_object* v___x_3742_; lean_object* v_bs_x27_3743_; size_t v___x_3744_; size_t v___x_3745_; lean_object* v___x_3746_; 
v_v_3741_ = lean_array_uget(v_bs_3739_, v_i_3738_);
v___x_3742_ = lean_unsigned_to_nat(0u);
v_bs_x27_3743_ = lean_array_uset(v_bs_3739_, v_i_3738_, v___x_3742_);
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_add(v_i_3738_, v___x_3744_);
v___x_3746_ = lean_array_uset(v_bs_x27_3743_, v_i_3738_, v_v_3741_);
v_i_3738_ = v___x_3745_;
v_bs_3739_ = v___x_3746_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3737_ = stack[0].m_num;
size_t v_i_3738_ = stack[1].m_num;
lean_object* v_bs_3739_ = stack[2].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_3737_, v_i_3738_, v_bs_3739_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3___boxed(lean_object* v_sz_3749_, lean_object* v_i_3750_, lean_object* v_bs_3751_){
_start:
{
size_t v_sz_boxed_3752_; size_t v_i_boxed_3753_; lean_object* v_res_3754_; 
v_sz_boxed_3752_ = lean_unbox_usize(v_sz_3749_);
lean_dec(v_sz_3749_);
v_i_boxed_3753_ = lean_unbox_usize(v_i_3750_);
lean_dec(v_i_3750_);
v_res_3754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_boxed_3752_, v_i_boxed_3753_, v_bs_3751_);
return v_res_3754_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(size_t v_sz_3755_, size_t v_i_3756_, lean_object* v_bs_3757_){
_start:
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_usize_dec_lt(v_i_3756_, v_sz_3755_);
if (v___x_3758_ == 0)
{
return v_bs_3757_;
}
else
{
lean_object* v_v_3759_; lean_object* v___x_3760_; lean_object* v_bs_x27_3761_; size_t v___x_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v_v_3759_ = lean_array_uget(v_bs_3757_, v_i_3756_);
v___x_3760_ = lean_unsigned_to_nat(0u);
v_bs_x27_3761_ = lean_array_uset(v_bs_3757_, v_i_3756_, v___x_3760_);
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_add(v_i_3756_, v___x_3762_);
v___x_3764_ = lean_array_uset(v_bs_x27_3761_, v_i_3756_, v_v_3759_);
v_i_3756_ = v___x_3763_;
v_bs_3757_ = v___x_3764_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3755_ = stack[0].m_num;
size_t v_i_3756_ = stack[1].m_num;
lean_object* v_bs_3757_ = stack[2].m_obj;
lean_object* v_res_3766_;
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_3755_, v_i_3756_, v_bs_3757_);
stack->m_obj
 = v_res_3766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6___boxed(lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_bs_3769_){
_start:
{
size_t v_sz_boxed_3770_; size_t v_i_boxed_3771_; lean_object* v_res_3772_; 
v_sz_boxed_3770_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3771_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_boxed_3770_, v_i_boxed_3771_, v_bs_3769_);
return v_res_3772_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(size_t v_sz_3773_, size_t v_i_3774_, lean_object* v_bs_3775_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_usize_dec_lt(v_i_3774_, v_sz_3773_);
if (v___x_3776_ == 0)
{
return v_bs_3775_;
}
else
{
lean_object* v_v_3777_; lean_object* v___x_3778_; lean_object* v_bs_x27_3779_; size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v_v_3777_ = lean_array_uget(v_bs_3775_, v_i_3774_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v_bs_x27_3779_ = lean_array_uset(v_bs_3775_, v_i_3774_, v___x_3778_);
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3774_, v___x_3780_);
v___x_3782_ = lean_array_uset(v_bs_x27_3779_, v_i_3774_, v_v_3777_);
v_i_3774_ = v___x_3781_;
v_bs_3775_ = v___x_3782_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3773_ = stack[0].m_num;
size_t v_i_3774_ = stack[1].m_num;
lean_object* v_bs_3775_ = stack[2].m_obj;
lean_object* v_res_3784_;
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_3773_, v_i_3774_, v_bs_3775_);
stack->m_obj
 = v_res_3784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5___boxed(lean_object* v_sz_3785_, lean_object* v_i_3786_, lean_object* v_bs_3787_){
_start:
{
size_t v_sz_boxed_3788_; size_t v_i_boxed_3789_; lean_object* v_res_3790_; 
v_sz_boxed_3788_ = lean_unbox_usize(v_sz_3785_);
lean_dec(v_sz_3785_);
v_i_boxed_3789_ = lean_unbox_usize(v_i_3786_);
lean_dec(v_i_3786_);
v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_boxed_3788_, v_i_boxed_3789_, v_bs_3787_);
return v_res_3790_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(lean_object* v_as_3791_, size_t v_i_3792_, size_t v_stop_3793_, lean_object* v_b_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_usize_dec_eq(v_i_3792_, v_stop_3793_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_array_uget_borrowed(v_as_3791_, v_i_3792_);
lean_inc(v___x_3798_);
v___x_3799_ = l___private_Lake_Config_Meta_0__Lake_mkParentFieldView(v___x_3798_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v_a_3801_; lean_object* v___x_3802_; size_t v___x_3803_; size_t v___x_3804_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
v_a_3801_ = lean_ctor_get(v___x_3799_, 1);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3799_, 2);
v___x_3802_ = lean_array_push(v_b_3794_, v_a_3800_);
v___x_3803_ = ((size_t)1ULL);
v___x_3804_ = lean_usize_add(v_i_3792_, v___x_3803_);
v_i_3792_ = v___x_3804_;
v_b_3794_ = v___x_3802_;
v___y_3796_ = v_a_3801_;
goto _start;
}
else
{
lean_object* v_a_3806_; lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v_b_3794_);
v_a_3806_ = lean_ctor_get(v___x_3799_, 0);
v_a_3807_ = lean_ctor_get(v___x_3799_, 1);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3799_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_inc(v_a_3806_);
lean_dec(v___x_3799_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3806_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_b_3794_);
lean_ctor_set(v___x_3815_, 1, v___y_3796_);
return v___x_3815_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3791_ = stack[0].m_obj;
size_t v_i_3792_ = stack[1].m_num;
size_t v_stop_3793_ = stack[2].m_num;
lean_object* v_b_3794_ = stack[3].m_obj;
lean_object* v___y_3795_ = stack[4].m_obj;
lean_object* v___y_3796_ = stack[5].m_obj;
lean_object* v_res_3816_;
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v_as_3791_, v_i_3792_, v_stop_3793_, v_b_3794_, v___y_3795_, v___y_3796_);
stack->m_obj
 = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8___boxed(lean_object* v_as_3817_, lean_object* v_i_3818_, lean_object* v_stop_3819_, lean_object* v_b_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
size_t v_i_boxed_3823_; size_t v_stop_boxed_3824_; lean_object* v_res_3825_; 
v_i_boxed_3823_ = lean_unbox_usize(v_i_3818_);
lean_dec(v_i_3818_);
v_stop_boxed_3824_ = lean_unbox_usize(v_stop_3819_);
lean_dec(v_stop_3819_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v_as_3817_, v_i_boxed_3823_, v_stop_boxed_3824_, v_b_3820_, v___y_3821_, v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v_as_3817_);
return v_res_3825_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(lean_object* v_as_3826_, size_t v_i_3827_, size_t v_stop_3828_, lean_object* v_b_3829_){
_start:
{
lean_object* v___y_3831_; uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_eq(v_i_3827_, v_stop_3828_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v_decl_x3f_3837_; 
v___x_3836_ = lean_array_uget_borrowed(v_as_3826_, v_i_3827_);
v_decl_x3f_3837_ = lean_ctor_get(v___x_3836_, 6);
if (lean_obj_tag(v_decl_x3f_3837_) == 0)
{
v___y_3831_ = v_b_3829_;
goto v___jp_3830_;
}
else
{
lean_object* v_val_3838_; lean_object* v___x_3839_; 
v_val_3838_ = lean_ctor_get(v_decl_x3f_3837_, 0);
lean_inc(v_val_3838_);
v___x_3839_ = lean_array_push(v_b_3829_, v_val_3838_);
v___y_3831_ = v___x_3839_;
goto v___jp_3830_;
}
}
else
{
return v_b_3829_;
}
v___jp_3830_:
{
size_t v___x_3832_; size_t v___x_3833_; 
v___x_3832_ = ((size_t)1ULL);
v___x_3833_ = lean_usize_add(v_i_3827_, v___x_3832_);
v_i_3827_ = v___x_3833_;
v_b_3829_ = v___y_3831_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3826_ = stack[0].m_obj;
size_t v_i_3827_ = stack[1].m_num;
size_t v_stop_3828_ = stack[2].m_num;
lean_object* v_b_3829_ = stack[3].m_obj;
lean_object* v_res_3840_;
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3826_, v_i_3827_, v_stop_3828_, v_b_3829_);
stack->m_obj
 = v_res_3840_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2___boxed(lean_object* v_as_3841_, lean_object* v_i_3842_, lean_object* v_stop_3843_, lean_object* v_b_3844_){
_start:
{
size_t v_i_boxed_3845_; size_t v_stop_boxed_3846_; lean_object* v_res_3847_; 
v_i_boxed_3845_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_stop_boxed_3846_ = lean_unbox_usize(v_stop_3843_);
lean_dec(v_stop_3843_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3841_, v_i_boxed_3845_, v_stop_boxed_3846_, v_b_3844_);
lean_dec_ref(v_as_3841_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(lean_object* v_as_3848_, lean_object* v_start_3849_, lean_object* v_stop_3850_){
_start:
{
lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3851_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___x_3852_ = lean_nat_dec_lt(v_start_3849_, v_stop_3850_);
if (v___x_3852_ == 0)
{
return v___x_3851_;
}
else
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = lean_array_get_size(v_as_3848_);
v___x_3854_ = lean_nat_dec_le(v_stop_3850_, v___x_3853_);
if (v___x_3854_ == 0)
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_nat_dec_lt(v_start_3849_, v___x_3853_);
if (v___x_3855_ == 0)
{
return v___x_3851_;
}
else
{
size_t v___x_3856_; size_t v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = lean_usize_of_nat(v_start_3849_);
v___x_3857_ = lean_usize_of_nat(v___x_3853_);
v___x_3858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3848_, v___x_3856_, v___x_3857_, v___x_3851_);
return v___x_3858_;
}
}
else
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_usize_of_nat(v_start_3849_);
v___x_3860_ = lean_usize_of_nat(v_stop_3850_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_expandConfigDecl_spec__2_spec__2(v_as_3848_, v___x_3859_, v___x_3860_, v___x_3851_);
return v___x_3861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2___boxed(lean_object* v_as_3862_, lean_object* v_start_3863_, lean_object* v_stop_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_as_3862_, v_start_3863_, v_stop_3864_);
lean_dec(v_stop_3864_);
lean_dec(v_start_3863_);
lean_dec_ref(v_as_3862_);
return v_res_3865_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(size_t v_sz_3866_, size_t v_i_3867_, lean_object* v_bs_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_lt(v_i_3867_, v_sz_3866_);
if (v___x_3869_ == 0)
{
return v_bs_3868_;
}
else
{
lean_object* v_v_3870_; lean_object* v___x_3871_; lean_object* v_bs_x27_3872_; size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v_v_3870_ = lean_array_uget(v_bs_3868_, v_i_3867_);
v___x_3871_ = lean_unsigned_to_nat(0u);
v_bs_x27_3872_ = lean_array_uset(v_bs_3868_, v_i_3867_, v___x_3871_);
v___x_3873_ = ((size_t)1ULL);
v___x_3874_ = lean_usize_add(v_i_3867_, v___x_3873_);
v___x_3875_ = lean_array_uset(v_bs_x27_3872_, v_i_3867_, v_v_3870_);
v_i_3867_ = v___x_3874_;
v_bs_3868_ = v___x_3875_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3866_ = stack[0].m_num;
size_t v_i_3867_ = stack[1].m_num;
lean_object* v_bs_3868_ = stack[2].m_obj;
lean_object* v_res_3877_;
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_3866_, v_i_3867_, v_bs_3868_);
stack->m_obj
 = v_res_3877_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7___boxed(lean_object* v_sz_3878_, lean_object* v_i_3879_, lean_object* v_bs_3880_){
_start:
{
size_t v_sz_boxed_3881_; size_t v_i_boxed_3882_; lean_object* v_res_3883_; 
v_sz_boxed_3881_ = lean_unbox_usize(v_sz_3878_);
lean_dec(v_sz_3878_);
v_i_boxed_3882_ = lean_unbox_usize(v_i_3879_);
lean_dec(v_i_3879_);
v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_boxed_3881_, v_i_boxed_3882_, v_bs_3880_);
return v_res_3883_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(size_t v_sz_3884_, size_t v_i_3885_, lean_object* v_bs_3886_){
_start:
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_usize_dec_lt(v_i_3885_, v_sz_3884_);
if (v___x_3887_ == 0)
{
return v_bs_3886_;
}
else
{
lean_object* v_v_3888_; lean_object* v___x_3889_; lean_object* v_bs_x27_3890_; lean_object* v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; lean_object* v___x_3894_; 
v_v_3888_ = lean_array_uget(v_bs_3886_, v_i_3885_);
v___x_3889_ = lean_unsigned_to_nat(0u);
v_bs_x27_3890_ = lean_array_uset(v_bs_3886_, v_i_3885_, v___x_3889_);
v___x_3891_ = l_Lake_BinderSyntaxView_mkArgument(v_v_3888_);
v___x_3892_ = ((size_t)1ULL);
v___x_3893_ = lean_usize_add(v_i_3885_, v___x_3892_);
v___x_3894_ = lean_array_uset(v_bs_x27_3890_, v_i_3885_, v___x_3891_);
v_i_3885_ = v___x_3893_;
v_bs_3886_ = v___x_3894_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3884_ = stack[0].m_num;
size_t v_i_3885_ = stack[1].m_num;
lean_object* v_bs_3886_ = stack[2].m_obj;
lean_object* v_res_3896_;
v_res_3896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_3884_, v_i_3885_, v_bs_3886_);
stack->m_obj
 = v_res_3896_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0___boxed(lean_object* v_sz_3897_, lean_object* v_i_3898_, lean_object* v_bs_3899_){
_start:
{
size_t v_sz_boxed_3900_; size_t v_i_boxed_3901_; lean_object* v_res_3902_; 
v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3897_);
lean_dec(v_sz_3897_);
v_i_boxed_3901_ = lean_unbox_usize(v_i_3898_);
lean_dec(v_i_3898_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_boxed_3900_, v_i_boxed_3901_, v_bs_3899_);
return v_res_3902_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(size_t v_sz_3903_, size_t v_i_3904_, lean_object* v_bs_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_usize_dec_lt(v_i_3904_, v_sz_3903_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v_bs_3905_);
lean_ctor_set(v___x_3909_, 1, v___y_3907_);
return v___x_3909_;
}
else
{
lean_object* v_v_3910_; lean_object* v___x_3911_; 
v_v_3910_ = lean_array_uget_borrowed(v_bs_3905_, v_i_3904_);
lean_inc(v_v_3910_);
v___x_3911_ = l___private_Lake_Config_Meta_0__Lake_mkFieldView(v_v_3910_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v_a_3913_; lean_object* v___x_3914_; lean_object* v_bs_x27_3915_; size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
v_a_3913_ = lean_ctor_get(v___x_3911_, 1);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3911_, 2);
v___x_3914_ = lean_unsigned_to_nat(0u);
v_bs_x27_3915_ = lean_array_uset(v_bs_3905_, v_i_3904_, v___x_3914_);
v___x_3916_ = ((size_t)1ULL);
v___x_3917_ = lean_usize_add(v_i_3904_, v___x_3916_);
v___x_3918_ = lean_array_uset(v_bs_x27_3915_, v_i_3904_, v_a_3912_);
v_i_3904_ = v___x_3917_;
v_bs_3905_ = v___x_3918_;
v___y_3907_ = v_a_3913_;
goto _start;
}
else
{
lean_object* v_a_3920_; lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v_bs_3905_);
v_a_3920_ = lean_ctor_get(v___x_3911_, 0);
v_a_3921_ = lean_ctor_get(v___x_3911_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3911_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_inc(v_a_3920_);
lean_dec(v___x_3911_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3920_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3903_ = stack[0].m_num;
size_t v_i_3904_ = stack[1].m_num;
lean_object* v_bs_3905_ = stack[2].m_obj;
lean_object* v___y_3906_ = stack[3].m_obj;
lean_object* v___y_3907_ = stack[4].m_obj;
lean_object* v_res_3929_;
v_res_3929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_3903_, v_i_3904_, v_bs_3905_, v___y_3906_, v___y_3907_);
stack->m_obj
 = v_res_3929_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1___boxed(lean_object* v_sz_3930_, lean_object* v_i_3931_, lean_object* v_bs_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
size_t v_sz_boxed_3935_; size_t v_i_boxed_3936_; lean_object* v_res_3937_; 
v_sz_boxed_3935_ = lean_unbox_usize(v_sz_3930_);
lean_dec(v_sz_3930_);
v_i_boxed_3936_ = lean_unbox_usize(v_i_3931_);
lean_dec(v_i_3931_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_boxed_3935_, v_i_boxed_3936_, v_bs_3932_, v___y_3933_, v___y_3934_);
lean_dec_ref(v___y_3933_);
return v_res_3937_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(size_t v_sz_3938_, size_t v_i_3939_, lean_object* v_bs_3940_){
_start:
{
uint8_t v___x_3941_; 
v___x_3941_ = lean_usize_dec_lt(v_i_3939_, v_sz_3938_);
if (v___x_3941_ == 0)
{
return v_bs_3940_;
}
else
{
lean_object* v_v_3942_; lean_object* v___x_3943_; lean_object* v_bs_x27_3944_; size_t v___x_3945_; size_t v___x_3946_; lean_object* v___x_3947_; 
v_v_3942_ = lean_array_uget(v_bs_3940_, v_i_3939_);
v___x_3943_ = lean_unsigned_to_nat(0u);
v_bs_x27_3944_ = lean_array_uset(v_bs_3940_, v_i_3939_, v___x_3943_);
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_add(v_i_3939_, v___x_3945_);
v___x_3947_ = lean_array_uset(v_bs_x27_3944_, v_i_3939_, v_v_3942_);
v_i_3939_ = v___x_3946_;
v_bs_3940_ = v___x_3947_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3938_ = stack[0].m_num;
size_t v_i_3939_ = stack[1].m_num;
lean_object* v_bs_3940_ = stack[2].m_obj;
lean_object* v_res_3949_;
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_3938_, v_i_3939_, v_bs_3940_);
stack->m_obj
 = v_res_3949_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4___boxed(lean_object* v_sz_3950_, lean_object* v_i_3951_, lean_object* v_bs_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3950_);
lean_dec(v_sz_3950_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3951_);
lean_dec(v_i_3951_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_boxed_3953_, v_i_boxed_3954_, v_bs_3952_);
return v_res_3955_;
}
}
static lean_object* _init_l_Lake_expandConfigDecl___closed__3(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_box(0);
v___x_3964_ = l_Lake_expandConfigDecl___lam__1(v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl(lean_object* v_stx_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Lake_configDecl___closed__1));
lean_inc(v_stx_3977_);
v___x_3981_ = l_Lean_Syntax_isOfKind(v_stx_3977_, v___x_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec(v_stx_3977_);
v___x_3982_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3983_ = l_Lean_Macro_throwError___redArg(v___x_3982_, v_a_3978_, v_a_3979_);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3984_ = lean_unsigned_to_nat(0u);
v___x_3985_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_3984_);
v___x_3986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__54));
lean_inc(v___x_3985_);
v___x_3987_ = l_Lean_Syntax_isOfKind(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_3988_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_3989_ = l_Lean_Macro_throwError___redArg(v___x_3988_, v_a_3978_, v_a_3979_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v_tk_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; size_t v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; size_t v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; size_t v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; size_t v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4149_; size_t v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4182_; lean_object* v___y_4183_; size_t v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v_a_4193_; lean_object* v_a_4194_; lean_object* v___y_4218_; lean_object* v___y_4219_; size_t v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4242_; lean_object* v___y_4243_; size_t v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4264_; size_t v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v_ctor_x3f_4300_; lean_object* v_fs_x3f_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v_ctor_x3f_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4347_; lean_object* v_ps_x3f_4348_; lean_object* v_xty_x3f_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v_xty_x3f_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v_ty_x3f_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_3990_ = lean_unsigned_to_nat(1u);
v_tk_4026_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_3990_);
v___x_4027_ = lean_unsigned_to_nat(2u);
v___x_4028_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4027_);
v___x_4294_ = lean_unsigned_to_nat(3u);
v___x_4295_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4294_);
v___x_4406_ = lean_unsigned_to_nat(4u);
v___x_4407_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4406_);
v___x_4408_ = l_Lean_Syntax_isNone(v___x_4407_);
if (v___x_4408_ == 0)
{
uint8_t v___x_4409_; 
lean_inc(v___x_4407_);
v___x_4409_ = l_Lean_Syntax_matchesNull(v___x_4407_, v___x_3990_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec(v___x_4407_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4410_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4411_ = l_Lean_Macro_throwError___redArg(v___x_4410_, v_a_3978_, v_a_3979_);
return v___x_4411_;
}
else
{
lean_object* v_ty_x3f_4412_; lean_object* v___x_4413_; 
v_ty_x3f_4412_ = l_Lean_Syntax_getArg(v___x_4407_, v___x_3984_);
lean_dec(v___x_4407_);
v___x_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4413_, 0, v_ty_x3f_4412_);
v_ty_x3f_4382_ = v___x_4413_;
v___y_4383_ = v_a_3978_;
v___y_4384_ = v_a_3979_;
goto v___jp_4381_;
}
}
else
{
lean_object* v___x_4414_; 
lean_dec(v___x_4407_);
v___x_4414_ = lean_box(0);
v_ty_x3f_4382_ = v___x_4414_;
v___y_4383_ = v_a_3978_;
v___y_4384_ = v_a_3979_;
goto v___jp_4381_;
}
v___jp_3991_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_array_get_size(v___y_3992_);
lean_dec_ref(v___y_3992_);
v___x_4002_ = l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls(v___y_4000_, v___y_3997_, v___x_4001_, v___y_3993_, v___y_3996_, v___y_3999_, v___y_3998_);
lean_dec_ref(v___y_3999_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4016_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
v_a_4004_ = lean_ctor_get(v___x_4002_, 1);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4006_ = v___x_4002_;
v_isShared_4007_ = v_isSharedCheck_4016_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_inc(v_a_4003_);
lean_dec(v___x_4002_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4016_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4008_ = lean_mk_empty_array_with_capacity(v___x_3990_);
v___x_4009_ = lean_array_push(v___x_4008_, v___y_3995_);
v___x_4010_ = l_Array_append___redArg(v___x_4009_, v_a_4003_);
lean_dec(v_a_4003_);
v___x_4011_ = lean_box(2);
lean_inc(v___y_3994_);
v___x_4012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
lean_ctor_set(v___x_4012_, 1, v___y_3994_);
lean_ctor_set(v___x_4012_, 2, v___x_4010_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4012_);
v___x_4014_ = v___x_4006_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_a_4004_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v___y_3995_);
v_a_4017_ = lean_ctor_get(v___x_4002_, 0);
v_a_4018_ = lean_ctor_get(v___x_4002_, 1);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4002_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_inc(v_a_4017_);
lean_dec(v___x_4002_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4017_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
v___jp_4029_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; size_t v_sz_4052_; lean_object* v___x_4053_; size_t v_sz_4054_; lean_object* v___x_4055_; size_t v_sz_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_inc_ref(v___y_4037_);
v___x_4049_ = l_Array_append___redArg(v___y_4037_, v___y_4048_);
lean_dec_ref(v___y_4048_);
lean_inc_n(v___y_4033_, 3);
lean_inc_n(v___y_4042_, 5);
v___x_4050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4050_, 0, v___y_4042_);
lean_ctor_set(v___x_4050_, 1, v___y_4033_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__2));
v_sz_4052_ = lean_array_size(v___y_4038_);
v___x_4053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__5(v_sz_4052_, v___y_4030_, v___y_4038_);
v_sz_4054_ = lean_array_size(v___x_4053_);
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__6(v_sz_4054_, v___y_4030_, v___x_4053_);
v_sz_4056_ = lean_array_size(v___x_4055_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__7(v_sz_4056_, v___y_4030_, v___x_4055_);
v___x_4058_ = l_Array_append___redArg(v___y_4037_, v___x_4057_);
lean_dec_ref(v___x_4057_);
v___x_4059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4059_, 0, v___y_4042_);
lean_ctor_set(v___x_4059_, 1, v___y_4033_);
lean_ctor_set(v___x_4059_, 2, v___x_4058_);
v___x_4060_ = l_Lean_Syntax_node1(v___y_4042_, v___x_4051_, v___x_4059_);
v___x_4061_ = l_Lean_Syntax_node3(v___y_4042_, v___y_4033_, v___y_4031_, v___x_4050_, v___x_4060_);
lean_inc(v___y_4035_);
v___x_4062_ = l_Lean_Syntax_node6(v___y_4042_, v___y_4035_, v___y_4043_, v___x_4028_, v___y_4046_, v___y_4036_, v___x_4061_, v___y_4047_);
lean_inc(v___x_3985_);
lean_inc(v___y_4034_);
v___x_4063_ = l_Lean_Syntax_node2(v___y_4042_, v___y_4034_, v___x_3985_, v___x_4062_);
v___x_4064_ = l_Lean_Syntax_getArg(v___x_3985_, v___x_4027_);
lean_dec(v___x_3985_);
v___x_4065_ = l_Lean_Syntax_getOptional_x3f(v___x_4064_);
lean_dec(v___x_4064_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_box(0);
v___y_3992_ = v___y_4039_;
v___y_3993_ = v___y_4032_;
v___y_3994_ = v___y_4033_;
v___y_3995_ = v___x_4063_;
v___y_3996_ = v___y_4041_;
v___y_3997_ = v___y_4040_;
v___y_3998_ = v___y_4045_;
v___y_3999_ = v___y_4044_;
v___y_4000_ = v___x_4066_;
goto v___jp_3991_;
}
else
{
lean_object* v_val_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_val_4067_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4065_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_val_4067_);
lean_dec(v___x_4065_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_val_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
v___y_3992_ = v___y_4039_;
v___y_3993_ = v___y_4032_;
v___y_3994_ = v___y_4033_;
v___y_3995_ = v___x_4063_;
v___y_3996_ = v___y_4041_;
v___y_3997_ = v___y_4040_;
v___y_3998_ = v___y_4045_;
v___y_3999_ = v___y_4044_;
v___y_4000_ = v___x_4072_;
goto v___jp_3991_;
}
}
}
}
v___jp_4075_:
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_4030_ = v___y_4076_;
v___y_4031_ = v___y_4077_;
v___y_4032_ = v___y_4078_;
v___y_4033_ = v___y_4079_;
v___y_4034_ = v___y_4080_;
v___y_4035_ = v___y_4081_;
v___y_4036_ = v___y_4082_;
v___y_4037_ = v___y_4083_;
v___y_4038_ = v___y_4084_;
v___y_4039_ = v___y_4085_;
v___y_4040_ = v___y_4087_;
v___y_4041_ = v___y_4088_;
v___y_4042_ = v___y_4089_;
v___y_4043_ = v___y_4086_;
v___y_4044_ = v___y_4091_;
v___y_4045_ = v___y_4090_;
v___y_4046_ = v___y_4093_;
v___y_4047_ = v___y_4092_;
v___y_4048_ = v___x_4094_;
goto v___jp_4029_;
}
v___jp_4095_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
lean_inc_ref(v___y_4104_);
v___x_4117_ = l_Array_append___redArg(v___y_4104_, v___y_4116_);
lean_dec_ref(v___y_4116_);
lean_inc_n(v___y_4099_, 2);
lean_inc_n(v___y_4109_, 4);
v___x_4118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4118_, 0, v___y_4109_);
lean_ctor_set(v___x_4118_, 1, v___y_4099_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
lean_inc(v___y_4113_);
v___x_4119_ = l_Lean_Syntax_node3(v___y_4109_, v___y_4113_, v___y_4103_, v___y_4097_, v___x_4118_);
v___x_4120_ = l_Lean_Syntax_node1(v___y_4109_, v___y_4099_, v___x_4119_);
v___x_4121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__3_spec__4___closed__40));
v___x_4122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___y_4109_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
if (lean_obj_tag(v___y_4102_) == 0)
{
v___y_4076_ = v___y_4096_;
v___y_4077_ = v___x_4122_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___y_4099_;
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4101_;
v___y_4082_ = v___x_4120_;
v___y_4083_ = v___y_4104_;
v___y_4084_ = v___y_4105_;
v___y_4085_ = v___y_4106_;
v___y_4086_ = v___y_4107_;
v___y_4087_ = v___y_4110_;
v___y_4088_ = v___y_4108_;
v___y_4089_ = v___y_4109_;
v___y_4090_ = v___y_4111_;
v___y_4091_ = v___y_4112_;
v___y_4092_ = v___y_4114_;
v___y_4093_ = v___y_4115_;
goto v___jp_4075_;
}
else
{
lean_object* v_val_4123_; 
v_val_4123_ = lean_ctor_get(v___y_4102_, 0);
lean_inc(v_val_4123_);
lean_dec_ref_known(v___y_4102_, 1);
if (lean_obj_tag(v_val_4123_) == 0)
{
v___y_4076_ = v___y_4096_;
v___y_4077_ = v___x_4122_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___y_4099_;
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4101_;
v___y_4082_ = v___x_4120_;
v___y_4083_ = v___y_4104_;
v___y_4084_ = v___y_4105_;
v___y_4085_ = v___y_4106_;
v___y_4086_ = v___y_4107_;
v___y_4087_ = v___y_4110_;
v___y_4088_ = v___y_4108_;
v___y_4089_ = v___y_4109_;
v___y_4090_ = v___y_4111_;
v___y_4091_ = v___y_4112_;
v___y_4092_ = v___y_4114_;
v___y_4093_ = v___y_4115_;
goto v___jp_4075_;
}
else
{
lean_object* v_val_4124_; lean_object* v___x_4125_; 
v_val_4124_ = lean_ctor_get(v_val_4123_, 0);
lean_inc(v_val_4124_);
lean_dec_ref_known(v_val_4123_, 1);
v___x_4125_ = l_Lake_expandConfigDecl___lam__0(v_val_4124_);
v___y_4030_ = v___y_4096_;
v___y_4031_ = v___x_4122_;
v___y_4032_ = v___y_4098_;
v___y_4033_ = v___y_4099_;
v___y_4034_ = v___y_4100_;
v___y_4035_ = v___y_4101_;
v___y_4036_ = v___x_4120_;
v___y_4037_ = v___y_4104_;
v___y_4038_ = v___y_4105_;
v___y_4039_ = v___y_4106_;
v___y_4040_ = v___y_4110_;
v___y_4041_ = v___y_4108_;
v___y_4042_ = v___y_4109_;
v___y_4043_ = v___y_4107_;
v___y_4044_ = v___y_4112_;
v___y_4045_ = v___y_4111_;
v___y_4046_ = v___y_4115_;
v___y_4047_ = v___y_4114_;
v___y_4048_ = v___x_4125_;
goto v___jp_4029_;
}
}
}
v___jp_4126_:
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_obj_once(&l_Lake_expandConfigDecl___closed__3, &l_Lake_expandConfigDecl___closed__3_once, _init_l_Lake_expandConfigDecl___closed__3);
v___y_4096_ = v___y_4127_;
v___y_4097_ = v___y_4128_;
v___y_4098_ = v___y_4129_;
v___y_4099_ = v___y_4130_;
v___y_4100_ = v___y_4131_;
v___y_4101_ = v___y_4132_;
v___y_4102_ = v___y_4133_;
v___y_4103_ = v___y_4134_;
v___y_4104_ = v___y_4135_;
v___y_4105_ = v___y_4136_;
v___y_4106_ = v___y_4137_;
v___y_4107_ = v___y_4140_;
v___y_4108_ = v___y_4141_;
v___y_4109_ = v___y_4139_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4144_;
v___y_4112_ = v___y_4143_;
v___y_4113_ = v___y_4142_;
v___y_4114_ = v___y_4146_;
v___y_4115_ = v___y_4145_;
v___y_4116_ = v___x_4147_;
goto v___jp_4095_;
}
v___jp_4148_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_inc_ref_n(v___y_4158_, 2);
v___x_4170_ = l_Array_append___redArg(v___y_4158_, v___y_4169_);
lean_dec_ref(v___y_4169_);
lean_inc_n(v___y_4152_, 2);
lean_inc_n(v___y_4165_, 4);
v___x_4171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4171_, 0, v___y_4165_);
lean_ctor_set(v___x_4171_, 1, v___y_4152_);
lean_ctor_set(v___x_4171_, 2, v___x_4170_);
lean_inc(v___y_4156_);
v___x_4172_ = l_Lean_Syntax_node2(v___y_4165_, v___y_4156_, v___y_4149_, v___x_4171_);
v___x_4173_ = ((lean_object*)(l_Lake_configDecl___closed__32));
v___x_4174_ = ((lean_object*)(l_Lake_configDecl___closed__33));
v___x_4175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___y_4165_);
lean_ctor_set(v___x_4175_, 1, v___x_4173_);
v___x_4176_ = l_Array_append___redArg(v___y_4158_, v___y_4157_);
lean_dec_ref(v___y_4157_);
v___x_4177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___y_4165_);
lean_ctor_set(v___x_4177_, 1, v___y_4152_);
lean_ctor_set(v___x_4177_, 2, v___x_4176_);
if (lean_obj_tag(v___y_4160_) == 0)
{
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___x_4177_;
v___y_4129_ = v___y_4151_;
v___y_4130_ = v___y_4152_;
v___y_4131_ = v___y_4153_;
v___y_4132_ = v___y_4154_;
v___y_4133_ = v___y_4155_;
v___y_4134_ = v___x_4175_;
v___y_4135_ = v___y_4158_;
v___y_4136_ = v___y_4159_;
v___y_4137_ = v___y_4161_;
v___y_4138_ = v___y_4162_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4164_;
v___y_4141_ = v___y_4163_;
v___y_4142_ = v___x_4174_;
v___y_4143_ = v___y_4166_;
v___y_4144_ = v___y_4167_;
v___y_4145_ = v___x_4172_;
v___y_4146_ = v___y_4168_;
goto v___jp_4126_;
}
else
{
lean_object* v_val_4178_; 
v_val_4178_ = lean_ctor_get(v___y_4160_, 0);
lean_inc(v_val_4178_);
lean_dec_ref_known(v___y_4160_, 1);
if (lean_obj_tag(v_val_4178_) == 0)
{
v___y_4127_ = v___y_4150_;
v___y_4128_ = v___x_4177_;
v___y_4129_ = v___y_4151_;
v___y_4130_ = v___y_4152_;
v___y_4131_ = v___y_4153_;
v___y_4132_ = v___y_4154_;
v___y_4133_ = v___y_4155_;
v___y_4134_ = v___x_4175_;
v___y_4135_ = v___y_4158_;
v___y_4136_ = v___y_4159_;
v___y_4137_ = v___y_4161_;
v___y_4138_ = v___y_4162_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4164_;
v___y_4141_ = v___y_4163_;
v___y_4142_ = v___x_4174_;
v___y_4143_ = v___y_4166_;
v___y_4144_ = v___y_4167_;
v___y_4145_ = v___x_4172_;
v___y_4146_ = v___y_4168_;
goto v___jp_4126_;
}
else
{
lean_object* v_val_4179_; lean_object* v___x_4180_; 
v_val_4179_ = lean_ctor_get(v_val_4178_, 0);
lean_inc(v_val_4179_);
lean_dec_ref_known(v_val_4178_, 1);
v___x_4180_ = l_Lake_expandConfigDecl___lam__0(v_val_4179_);
v___y_4096_ = v___y_4150_;
v___y_4097_ = v___x_4177_;
v___y_4098_ = v___y_4151_;
v___y_4099_ = v___y_4152_;
v___y_4100_ = v___y_4153_;
v___y_4101_ = v___y_4154_;
v___y_4102_ = v___y_4155_;
v___y_4103_ = v___x_4175_;
v___y_4104_ = v___y_4158_;
v___y_4105_ = v___y_4159_;
v___y_4106_ = v___y_4161_;
v___y_4107_ = v___y_4164_;
v___y_4108_ = v___y_4163_;
v___y_4109_ = v___y_4165_;
v___y_4110_ = v___y_4162_;
v___y_4111_ = v___y_4167_;
v___y_4112_ = v___y_4166_;
v___y_4113_ = v___x_4174_;
v___y_4114_ = v___y_4168_;
v___y_4115_ = v___x_4172_;
v___y_4116_ = v___x_4180_;
goto v___jp_4095_;
}
}
}
v___jp_4181_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; size_t v_sz_4208_; lean_object* v___x_4209_; size_t v_sz_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4195_ = lean_array_get_size(v_a_4193_);
v___x_4196_ = l_Array_filterMapM___at___00Lake_expandConfigDecl_spec__2(v_a_4193_, v___x_3984_, v___x_4195_);
v___x_4197_ = 0;
v___x_4198_ = l_Lean_SourceInfo_fromRef(v___y_4183_, v___x_4197_);
lean_dec(v___y_4183_);
v___x_4199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__53));
v___x_4200_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__4));
v___x_4201_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__5));
v___x_4202_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__7));
lean_inc_n(v___x_4198_, 3);
v___x_4203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4198_);
lean_ctor_set(v___x_4203_, 1, v___x_4200_);
v___x_4204_ = l_Lean_Syntax_node1(v___x_4198_, v___x_4202_, v___x_4203_);
v___x_4205_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkFieldView___closed__3));
v___x_4206_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__4));
v___x_4207_ = lean_obj_once(&l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5, &l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5_once, _init_l___private_Lake_Config_Meta_0__Lake_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil__lake___lam__0___closed__5);
v_sz_4208_ = lean_array_size(v___y_4186_);
lean_inc_ref(v___y_4186_);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__3(v_sz_4208_, v___y_4184_, v___y_4186_);
v_sz_4210_ = lean_array_size(v___x_4209_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__4(v_sz_4210_, v___y_4184_, v___x_4209_);
v___x_4212_ = l_Array_append___redArg(v___x_4207_, v___x_4211_);
lean_dec_ref(v___x_4211_);
v___x_4213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4198_);
lean_ctor_set(v___x_4213_, 1, v___x_4206_);
lean_ctor_set(v___x_4213_, 2, v___x_4212_);
if (lean_obj_tag(v___y_4189_) == 1)
{
lean_object* v_val_4214_; lean_object* v___x_4215_; 
v_val_4214_ = lean_ctor_get(v___y_4189_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v___y_4189_, 1);
v___x_4215_ = l_Array_mkArray1___redArg(v_val_4214_);
v___y_4149_ = v___x_4213_;
v___y_4150_ = v___y_4184_;
v___y_4151_ = v___y_4187_;
v___y_4152_ = v___x_4206_;
v___y_4153_ = v___x_4199_;
v___y_4154_ = v___x_4201_;
v___y_4155_ = v___y_4188_;
v___y_4156_ = v___x_4205_;
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___x_4207_;
v___y_4159_ = v___x_4196_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v_a_4193_;
v___y_4164_ = v___x_4204_;
v___y_4165_ = v___x_4198_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v_a_4194_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___x_4215_;
goto v___jp_4148_;
}
else
{
lean_object* v___x_4216_; 
lean_dec(v___y_4189_);
v___x_4216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls_spec__2_spec__2___closed__55));
v___y_4149_ = v___x_4213_;
v___y_4150_ = v___y_4184_;
v___y_4151_ = v___y_4187_;
v___y_4152_ = v___x_4206_;
v___y_4153_ = v___x_4199_;
v___y_4154_ = v___x_4201_;
v___y_4155_ = v___y_4188_;
v___y_4156_ = v___x_4205_;
v___y_4157_ = v___y_4182_;
v___y_4158_ = v___x_4207_;
v___y_4159_ = v___x_4196_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4186_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v_a_4193_;
v___y_4164_ = v___x_4204_;
v___y_4165_ = v___x_4198_;
v___y_4166_ = v___y_4191_;
v___y_4167_ = v_a_4194_;
v___y_4168_ = v___y_4192_;
v___y_4169_ = v___x_4216_;
goto v___jp_4148_;
}
}
v___jp_4217_:
{
if (lean_obj_tag(v___y_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v_a_4231_; 
v_a_4230_ = lean_ctor_get(v___y_4229_, 0);
lean_inc(v_a_4230_);
v_a_4231_ = lean_ctor_get(v___y_4229_, 1);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___y_4229_, 2);
v___y_4182_ = v___y_4219_;
v___y_4183_ = v___y_4218_;
v___y_4184_ = v___y_4220_;
v___y_4185_ = v___y_4222_;
v___y_4186_ = v___y_4221_;
v___y_4187_ = v___y_4223_;
v___y_4188_ = v___y_4224_;
v___y_4189_ = v___y_4226_;
v___y_4190_ = v___y_4225_;
v___y_4191_ = v___y_4227_;
v___y_4192_ = v___y_4228_;
v_a_4193_ = v_a_4230_;
v_a_4194_ = v_a_4231_;
goto v___jp_4181_;
}
else
{
lean_object* v_a_4232_; lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___x_4028_);
lean_dec(v___x_3985_);
v_a_4232_ = lean_ctor_get(v___y_4229_, 0);
v_a_4233_ = lean_ctor_get(v___y_4229_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___y_4229_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___y_4229_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_inc(v_a_4232_);
lean_dec(v___y_4229_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4232_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
v___jp_4241_:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4255_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_4254_);
v___x_4256_ = lean_array_get_size(v___x_4255_);
v___x_4257_ = lean_nat_dec_lt(v___x_3984_, v___x_4256_);
if (v___x_4257_ == 0)
{
lean_dec_ref(v___x_4255_);
v___y_4182_ = v___y_4254_;
v___y_4183_ = v___y_4242_;
v___y_4184_ = v___y_4244_;
v___y_4185_ = v___y_4247_;
v___y_4186_ = v___y_4246_;
v___y_4187_ = v___y_4248_;
v___y_4188_ = v___y_4249_;
v___y_4189_ = v___y_4251_;
v___y_4190_ = v___y_4250_;
v___y_4191_ = v___y_4252_;
v___y_4192_ = v___y_4253_;
v_a_4193_ = v___y_4243_;
v_a_4194_ = v___y_4245_;
goto v___jp_4181_;
}
else
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_nat_dec_le(v___x_4256_, v___x_4256_);
if (v___x_4258_ == 0)
{
if (v___x_4257_ == 0)
{
lean_dec_ref(v___x_4255_);
v___y_4182_ = v___y_4254_;
v___y_4183_ = v___y_4242_;
v___y_4184_ = v___y_4244_;
v___y_4185_ = v___y_4247_;
v___y_4186_ = v___y_4246_;
v___y_4187_ = v___y_4248_;
v___y_4188_ = v___y_4249_;
v___y_4189_ = v___y_4251_;
v___y_4190_ = v___y_4250_;
v___y_4191_ = v___y_4252_;
v___y_4192_ = v___y_4253_;
v_a_4193_ = v___y_4243_;
v_a_4194_ = v___y_4245_;
goto v___jp_4181_;
}
else
{
size_t v___x_4259_; lean_object* v___x_4260_; 
v___x_4259_ = lean_usize_of_nat(v___x_4256_);
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v___x_4255_, v___y_4244_, v___x_4259_, v___y_4243_, v___y_4252_, v___y_4245_);
lean_dec_ref(v___x_4255_);
v___y_4218_ = v___y_4242_;
v___y_4219_ = v___y_4254_;
v___y_4220_ = v___y_4244_;
v___y_4221_ = v___y_4246_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v___y_4249_;
v___y_4225_ = v___y_4250_;
v___y_4226_ = v___y_4251_;
v___y_4227_ = v___y_4252_;
v___y_4228_ = v___y_4253_;
v___y_4229_ = v___x_4260_;
goto v___jp_4217_;
}
}
else
{
size_t v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = lean_usize_of_nat(v___x_4256_);
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandConfigDecl_spec__8(v___x_4255_, v___y_4244_, v___x_4261_, v___y_4243_, v___y_4252_, v___y_4245_);
lean_dec_ref(v___x_4255_);
v___y_4218_ = v___y_4242_;
v___y_4219_ = v___y_4254_;
v___y_4220_ = v___y_4244_;
v___y_4221_ = v___y_4246_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v___y_4249_;
v___y_4225_ = v___y_4250_;
v___y_4226_ = v___y_4251_;
v___y_4227_ = v___y_4252_;
v___y_4228_ = v___y_4253_;
v___y_4229_ = v___x_4262_;
goto v___jp_4217_;
}
}
}
v___jp_4263_:
{
size_t v_sz_4277_; lean_object* v___x_4278_; 
v_sz_4277_ = lean_array_size(v___y_4276_);
v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__1(v_sz_4277_, v___y_4265_, v___y_4276_, v___y_4274_, v___y_4270_);
if (lean_obj_tag(v___x_4278_) == 0)
{
if (lean_obj_tag(v___y_4266_) == 0)
{
lean_object* v_a_4279_; lean_object* v_a_4280_; lean_object* v___x_4281_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
v_a_4280_ = lean_ctor_get(v___x_4278_, 1);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4278_, 2);
v___x_4281_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4242_ = v___y_4264_;
v___y_4243_ = v_a_4279_;
v___y_4244_ = v___y_4265_;
v___y_4245_ = v_a_4280_;
v___y_4246_ = v___y_4268_;
v___y_4247_ = v___y_4267_;
v___y_4248_ = v___y_4269_;
v___y_4249_ = v___y_4271_;
v___y_4250_ = v___y_4273_;
v___y_4251_ = v___y_4272_;
v___y_4252_ = v___y_4274_;
v___y_4253_ = v___y_4275_;
v___y_4254_ = v___x_4281_;
goto v___jp_4241_;
}
else
{
lean_object* v_a_4282_; lean_object* v_a_4283_; lean_object* v_val_4284_; 
v_a_4282_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4282_);
v_a_4283_ = lean_ctor_get(v___x_4278_, 1);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4278_, 2);
v_val_4284_ = lean_ctor_get(v___y_4266_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v___y_4266_, 1);
v___y_4242_ = v___y_4264_;
v___y_4243_ = v_a_4282_;
v___y_4244_ = v___y_4265_;
v___y_4245_ = v_a_4283_;
v___y_4246_ = v___y_4268_;
v___y_4247_ = v___y_4267_;
v___y_4248_ = v___y_4269_;
v___y_4249_ = v___y_4271_;
v___y_4250_ = v___y_4273_;
v___y_4251_ = v___y_4272_;
v___y_4252_ = v___y_4274_;
v___y_4253_ = v___y_4275_;
v___y_4254_ = v_val_4284_;
goto v___jp_4241_;
}
}
else
{
lean_object* v_a_4285_; lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4264_);
lean_dec(v___x_4028_);
lean_dec(v___x_3985_);
v_a_4285_ = lean_ctor_get(v___x_4278_, 0);
v_a_4286_ = lean_ctor_get(v___x_4278_, 1);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4278_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_inc(v_a_4285_);
lean_dec(v___x_4278_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4285_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
v___jp_4296_:
{
lean_object* v_methods_4304_; lean_object* v_quotContext_4305_; lean_object* v_currMacroScope_4306_; lean_object* v_currRecDepth_4307_; lean_object* v_maxRecDepth_4308_; lean_object* v_ref_4309_; lean_object* v_bs_4310_; lean_object* v_ref_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_methods_4304_ = lean_ctor_get(v___y_4302_, 0);
v_quotContext_4305_ = lean_ctor_get(v___y_4302_, 1);
v_currMacroScope_4306_ = lean_ctor_get(v___y_4302_, 2);
v_currRecDepth_4307_ = lean_ctor_get(v___y_4302_, 3);
v_maxRecDepth_4308_ = lean_ctor_get(v___y_4302_, 4);
v_ref_4309_ = lean_ctor_get(v___y_4302_, 5);
v_bs_4310_ = l_Lean_Syntax_getArgs(v___x_4295_);
lean_dec(v___x_4295_);
v_ref_4311_ = l_Lean_replaceRef(v_tk_4026_, v_ref_4309_);
lean_dec(v_tk_4026_);
lean_inc(v_ref_4311_);
lean_inc(v_maxRecDepth_4308_);
lean_inc(v_currRecDepth_4307_);
lean_inc(v_currMacroScope_4306_);
lean_inc(v_quotContext_4305_);
lean_inc(v_methods_4304_);
v___x_4312_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4312_, 0, v_methods_4304_);
lean_ctor_set(v___x_4312_, 1, v_quotContext_4305_);
lean_ctor_set(v___x_4312_, 2, v_currMacroScope_4306_);
lean_ctor_set(v___x_4312_, 3, v_currRecDepth_4307_);
lean_ctor_set(v___x_4312_, 4, v_maxRecDepth_4308_);
lean_ctor_set(v___x_4312_, 5, v_ref_4311_);
v___x_4313_ = l_Lake_expandBinders(v_bs_4310_, v___x_4312_, v___y_4303_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; size_t v_sz_4319_; size_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
v_a_4315_ = lean_ctor_get(v___x_4313_, 1);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4313_, 2);
v___x_4316_ = lean_unsigned_to_nat(7u);
v___x_4317_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4316_);
lean_dec(v_stx_3977_);
v___x_4318_ = l_Lean_Syntax_getArg(v___x_4028_, v___x_3984_);
v_sz_4319_ = lean_array_size(v_a_4314_);
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_expandConfigDecl_spec__0(v_sz_4319_, v___x_4320_, v_a_4314_);
lean_inc(v___x_4318_);
v___x_4322_ = l_Lean_Syntax_mkApp(v___x_4318_, v___x_4321_);
if (lean_obj_tag(v_fs_x3f_4301_) == 0)
{
lean_object* v___x_4323_; 
v___x_4323_ = ((lean_object*)(l___private_Lake_Config_Meta_0__Lake_mkConfigAuxDecls___closed__6));
v___y_4264_ = v_ref_4311_;
v___y_4265_ = v___x_4320_;
v___y_4266_ = v___y_4297_;
v___y_4267_ = v___y_4298_;
v___y_4268_ = v_bs_4310_;
v___y_4269_ = v___x_4322_;
v___y_4270_ = v_a_4315_;
v___y_4271_ = v_ctor_x3f_4300_;
v___y_4272_ = v___y_4299_;
v___y_4273_ = v___x_4318_;
v___y_4274_ = v___x_4312_;
v___y_4275_ = v___x_4317_;
v___y_4276_ = v___x_4323_;
goto v___jp_4263_;
}
else
{
lean_object* v_val_4324_; 
v_val_4324_ = lean_ctor_get(v_fs_x3f_4301_, 0);
lean_inc(v_val_4324_);
lean_dec_ref_known(v_fs_x3f_4301_, 1);
v___y_4264_ = v_ref_4311_;
v___y_4265_ = v___x_4320_;
v___y_4266_ = v___y_4297_;
v___y_4267_ = v___y_4298_;
v___y_4268_ = v_bs_4310_;
v___y_4269_ = v___x_4322_;
v___y_4270_ = v_a_4315_;
v___y_4271_ = v_ctor_x3f_4300_;
v___y_4272_ = v___y_4299_;
v___y_4273_ = v___x_4318_;
v___y_4274_ = v___x_4312_;
v___y_4275_ = v___x_4317_;
v___y_4276_ = v_val_4324_;
goto v___jp_4263_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref_known(v___x_4312_, 6);
lean_dec(v_ref_4311_);
lean_dec_ref(v_bs_4310_);
lean_dec(v_fs_x3f_4301_);
lean_dec(v_ctor_x3f_4300_);
lean_dec(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec(v___x_4028_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v_a_4325_ = lean_ctor_get(v___x_4313_, 0);
v_a_4326_ = lean_ctor_get(v___x_4313_, 1);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4313_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_inc(v_a_4325_);
lean_dec(v___x_4313_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4325_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
v___jp_4334_:
{
lean_object* v___x_4342_; lean_object* v_fs_x3f_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4342_ = l_Lean_Syntax_getArg(v___y_4338_, v___x_4027_);
lean_dec(v___y_4338_);
v_fs_x3f_4343_ = l_Lean_Syntax_getArgs(v___x_4342_);
lean_dec(v___x_4342_);
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_ctor_x3f_4339_);
v___x_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4345_, 0, v_fs_x3f_4343_);
v___y_4297_ = v___y_4335_;
v___y_4298_ = v___y_4336_;
v___y_4299_ = v___y_4337_;
v_ctor_x3f_4300_ = v___x_4344_;
v_fs_x3f_4301_ = v___x_4345_;
v___y_4302_ = v___y_4340_;
v___y_4303_ = v___y_4341_;
goto v___jp_4296_;
}
v___jp_4346_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4352_ = lean_unsigned_to_nat(6u);
v___x_4353_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4352_);
v___x_4354_ = l_Lean_Syntax_isNone(v___x_4353_);
if (v___x_4354_ == 0)
{
uint8_t v___x_4355_; 
lean_inc(v___x_4353_);
v___x_4355_ = l_Lean_Syntax_matchesNull(v___x_4353_, v___x_4294_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_dec(v___x_4353_);
lean_dec(v_xty_x3f_4349_);
lean_dec(v_ps_x3f_4348_);
lean_dec(v___y_4347_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4356_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4357_ = l_Lean_Macro_throwError___redArg(v___x_4356_, v___y_4350_, v___y_4351_);
return v___x_4357_;
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4358_ = l_Lean_Syntax_getArg(v___x_4353_, v___x_3984_);
v___x_4359_ = ((lean_object*)(l_Lake_configDecl___closed__45));
v___x_4360_ = l_Lean_Syntax_isOfKind(v___x_4358_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec(v___x_4353_);
lean_dec(v_xty_x3f_4349_);
lean_dec(v_ps_x3f_4348_);
lean_dec(v___y_4347_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4361_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4362_ = l_Lean_Macro_throwError___redArg(v___x_4361_, v___y_4350_, v___y_4351_);
return v___x_4362_;
}
else
{
lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4363_ = l_Lean_Syntax_getArg(v___x_4353_, v___x_3990_);
v___x_4364_ = l_Lean_Syntax_isNone(v___x_4363_);
if (v___x_4364_ == 0)
{
uint8_t v___x_4365_; 
lean_inc(v___x_4363_);
v___x_4365_ = l_Lean_Syntax_matchesNull(v___x_4363_, v___x_3990_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
lean_dec(v___x_4363_);
lean_dec(v___x_4353_);
lean_dec(v_xty_x3f_4349_);
lean_dec(v_ps_x3f_4348_);
lean_dec(v___y_4347_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4366_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4367_ = l_Lean_Macro_throwError___redArg(v___x_4366_, v___y_4350_, v___y_4351_);
return v___x_4367_;
}
else
{
lean_object* v_ctor_x3f_4368_; lean_object* v___x_4369_; 
v_ctor_x3f_4368_ = l_Lean_Syntax_getArg(v___x_4363_, v___x_3984_);
lean_dec(v___x_4363_);
v___x_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4369_, 0, v_ctor_x3f_4368_);
v___y_4335_ = v_ps_x3f_4348_;
v___y_4336_ = v_xty_x3f_4349_;
v___y_4337_ = v___y_4347_;
v___y_4338_ = v___x_4353_;
v_ctor_x3f_4339_ = v___x_4369_;
v___y_4340_ = v___y_4350_;
v___y_4341_ = v___y_4351_;
goto v___jp_4334_;
}
}
else
{
lean_object* v___x_4370_; 
lean_dec(v___x_4363_);
v___x_4370_ = lean_box(0);
v___y_4335_ = v_ps_x3f_4348_;
v___y_4336_ = v_xty_x3f_4349_;
v___y_4337_ = v___y_4347_;
v___y_4338_ = v___x_4353_;
v_ctor_x3f_4339_ = v___x_4370_;
v___y_4340_ = v___y_4350_;
v___y_4341_ = v___y_4351_;
goto v___jp_4334_;
}
}
}
}
else
{
lean_object* v___x_4371_; 
lean_dec(v___x_4353_);
v___x_4371_ = lean_box(0);
v___y_4297_ = v_ps_x3f_4348_;
v___y_4298_ = v_xty_x3f_4349_;
v___y_4299_ = v___y_4347_;
v_ctor_x3f_4300_ = v___x_4371_;
v_fs_x3f_4301_ = v___x_4371_;
v___y_4302_ = v___y_4350_;
v___y_4303_ = v___y_4351_;
goto v___jp_4296_;
}
}
v___jp_4372_:
{
lean_object* v_ps_x3f_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_ps_x3f_4378_ = l_Lean_Syntax_getArgs(v___y_4373_);
lean_dec(v___y_4373_);
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v_ps_x3f_4378_);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v_xty_x3f_4375_);
v___y_4347_ = v___y_4374_;
v_ps_x3f_4348_ = v___x_4379_;
v_xty_x3f_4349_ = v___x_4380_;
v___y_4350_ = v___y_4376_;
v___y_4351_ = v___y_4377_;
goto v___jp_4346_;
}
v___jp_4381_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4385_ = lean_unsigned_to_nat(5u);
v___x_4386_ = l_Lean_Syntax_getArg(v_stx_3977_, v___x_4385_);
v___x_4387_ = l_Lean_Syntax_isNone(v___x_4386_);
if (v___x_4387_ == 0)
{
uint8_t v___x_4388_; 
lean_inc(v___x_4386_);
v___x_4388_ = l_Lean_Syntax_matchesNull(v___x_4386_, v___x_3990_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
lean_dec(v___x_4386_);
lean_dec(v_ty_x3f_4382_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4389_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4390_ = l_Lean_Macro_throwError___redArg(v___x_4389_, v___y_4383_, v___y_4384_);
return v___x_4390_;
}
else
{
lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4391_ = l_Lean_Syntax_getArg(v___x_4386_, v___x_3984_);
lean_dec(v___x_4386_);
v___x_4392_ = ((lean_object*)(l_Lake_configDecl___closed__33));
lean_inc(v___x_4391_);
v___x_4393_ = l_Lean_Syntax_isOfKind(v___x_4391_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec(v___x_4391_);
lean_dec(v_ty_x3f_4382_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4394_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4395_ = l_Lean_Macro_throwError___redArg(v___x_4394_, v___y_4383_, v___y_4384_);
return v___x_4395_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = l_Lean_Syntax_getArg(v___x_4391_, v___x_3990_);
v___x_4397_ = l_Lean_Syntax_getArg(v___x_4391_, v___x_4027_);
lean_dec(v___x_4391_);
v___x_4398_ = l_Lean_Syntax_isNone(v___x_4397_);
if (v___x_4398_ == 0)
{
uint8_t v___x_4399_; 
lean_inc(v___x_4397_);
v___x_4399_ = l_Lean_Syntax_matchesNull(v___x_4397_, v___x_3990_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_dec(v___x_4397_);
lean_dec(v___x_4396_);
lean_dec(v_ty_x3f_4382_);
lean_dec(v___x_4295_);
lean_dec(v___x_4028_);
lean_dec(v_tk_4026_);
lean_dec(v___x_3985_);
lean_dec(v_stx_3977_);
v___x_4400_ = ((lean_object*)(l_Lake_expandConfigDecl___closed__0));
v___x_4401_ = l_Lean_Macro_throwError___redArg(v___x_4400_, v___y_4383_, v___y_4384_);
return v___x_4401_;
}
else
{
lean_object* v_xty_x3f_4402_; lean_object* v___x_4403_; 
v_xty_x3f_4402_ = l_Lean_Syntax_getArg(v___x_4397_, v___x_3984_);
lean_dec(v___x_4397_);
v___x_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4403_, 0, v_xty_x3f_4402_);
v___y_4373_ = v___x_4396_;
v___y_4374_ = v_ty_x3f_4382_;
v_xty_x3f_4375_ = v___x_4403_;
v___y_4376_ = v___y_4383_;
v___y_4377_ = v___y_4384_;
goto v___jp_4372_;
}
}
else
{
lean_object* v___x_4404_; 
lean_dec(v___x_4397_);
v___x_4404_ = lean_box(0);
v___y_4373_ = v___x_4396_;
v___y_4374_ = v_ty_x3f_4382_;
v_xty_x3f_4375_ = v___x_4404_;
v___y_4376_ = v___y_4383_;
v___y_4377_ = v___y_4384_;
goto v___jp_4372_;
}
}
}
}
else
{
lean_object* v___x_4405_; 
lean_dec(v___x_4386_);
v___x_4405_ = lean_box(0);
v___y_4347_ = v_ty_x3f_4382_;
v_ps_x3f_4348_ = v___x_4405_;
v_xty_x3f_4349_ = v___x_4405_;
v___y_4350_ = v___y_4383_;
v___y_4351_ = v___y_4384_;
goto v___jp_4346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandConfigDecl___boxed(lean_object* v_stx_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lake_expandConfigDecl(v_stx_4415_, v_a_4416_, v_a_4417_);
lean_dec_ref(v_a_4416_);
return v_res_4418_;
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
