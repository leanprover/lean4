// Lean compiler output
// Module: Lake.Util.OpaqueType
// Imports: public meta import Lake.Util.Binder public import Init.Prelude
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lake_expandBinders(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object*);
lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__0 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__0_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nonemptyTypeCmd"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__1 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__1_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__2_value_aux_0),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 29, 126, 4, 221, 16, 76, 39)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__2 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__2_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__3 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__3_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__4 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__5 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__5_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__6 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__6_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__7 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__7_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__8 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__8_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__8_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__9 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__9_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__6_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__9_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__10 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__10_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "visibility"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__11 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__11_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 205, 25, 140, 55, 50, 241, 254)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__12 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__12_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__12_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__13 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__13_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__6_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__13_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__14 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__14_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__10_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__14_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__15 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__15_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "nonempty_type "};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__16 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__16_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__16_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__17 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__17_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__15_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__17_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__18 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__18_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__19 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__19_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__20 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__20_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__20_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__21 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__21_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__18_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__21_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__22 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__22_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__23 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__23_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__23_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__24 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__24_value;
static const lean_string_object l_Lake_nonemptyTypeCmd___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binder"};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__25 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__25_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__26_value_aux_0),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(90, 139, 132, 2, 118, 46, 191, 226)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__26 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__26_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__26_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__27 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__27_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__24_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__27_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__28 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__28_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__22_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__28_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__29 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__29_value;
static const lean_ctor_object l_Lake_nonemptyTypeCmd___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__29_value)}};
static const lean_object* l_Lake_nonemptyTypeCmd___closed__30 = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__30_value;
LEAN_EXPORT const lean_object* l_Lake_nonemptyTypeCmd = (const lean_object*)&l_Lake_nonemptyTypeCmd___closed__30_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonemptyType"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(lean_object*);
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instNonempty"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Type"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|>."};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "property"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(89, 150, 111, 5, 6, 150, 149, 192)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value;
static const lean_array_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value;
static const lean_array_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "explicitUniv"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(206, 217, 218, 63, 82, 102, 26, 62)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NonemptyType"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(87, 253, 156, 237, 229, 153, 40, 17)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".{"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_hydrateOpaqueTypeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "hydrateOpaqueTypeCmd"};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__0 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__0_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 247, 39, 29, 239, 7, 87, 22)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__1 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__1_value;
static const lean_string_object l_Lake_hydrateOpaqueTypeCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "hydrate_opaque_type "};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__2 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__2_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__2_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__3 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__3_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__14_value),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__3_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__4 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__4_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__4_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__21_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__5 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__5_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__5_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__21_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__6 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__6_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__24_value),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__21_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__7 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__7_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_nonemptyTypeCmd___closed__4_value),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__6_value),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__7_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__8 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__8_value;
static const lean_ctor_object l_Lake_hydrateOpaqueTypeCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__8_value)}};
static const lean_object* l_Lake_hydrateOpaqueTypeCmd___closed__9 = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_hydrateOpaqueTypeCmd = (const lean_object*)&l_Lake_hydrateOpaqueTypeCmd___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Coe"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 70, 184, 182, 52, 50, 221, 222)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_nonemptyTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 247, 82, 130, 198, 123, 173)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unsafeMk"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(17, 66, 223, 134, 53, 49, 169, 208)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instCoeMk"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(188, 43, 242, 158, 192, 163, 123, 89)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(149, 195, 233, 5, 41, 184, 182, 9)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unsafeGet"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(172, 192, 107, 19, 95, 77, 28, 221)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instCoeGet"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(4, 9, 13, 81, 139, 59, 11, 128)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(79, 160, 60, 55, 136, 115, 80, 144)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unsafeCast"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(190, 168, 242, 108, 36, 6, 114, 127)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value;
static const lean_string_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82;
static const lean_ctor_object l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83 = (const lean_object*)&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0));
v___x_72_ = l_Lean_Name_str___override(v_x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0));
v___x_76_ = l_Lean_Name_str___override(v_x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(size_t v_sz_77_, size_t v_i_78_, lean_object* v_bs_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_usize_dec_lt(v_i_78_, v_sz_77_);
if (v___x_80_ == 0)
{
return v_bs_79_;
}
else
{
lean_object* v_v_81_; lean_object* v___x_82_; lean_object* v_bs_x27_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v_v_81_ = lean_array_uget(v_bs_79_, v_i_78_);
v___x_82_ = lean_unsigned_to_nat(0u);
v_bs_x27_83_ = lean_array_uset(v_bs_79_, v_i_78_, v___x_82_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_add(v_i_78_, v___x_84_);
v___x_86_ = lean_array_uset(v_bs_x27_83_, v_i_78_, v_v_81_);
v_i_78_ = v___x_85_;
v_bs_79_ = v___x_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1___boxed(lean_object* v_sz_88_, lean_object* v_i_89_, lean_object* v_bs_90_){
_start:
{
size_t v_sz_boxed_91_; size_t v_i_boxed_92_; lean_object* v_res_93_; 
v_sz_boxed_91_ = lean_unbox_usize(v_sz_88_);
lean_dec(v_sz_88_);
v_i_boxed_92_ = lean_unbox_usize(v_i_89_);
lean_dec(v_i_89_);
v_res_93_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_boxed_91_, v_i_boxed_92_, v_bs_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(size_t v_sz_94_, size_t v_i_95_, lean_object* v_bs_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_95_, v_sz_94_);
if (v___x_97_ == 0)
{
return v_bs_96_;
}
else
{
lean_object* v_v_98_; lean_object* v___x_99_; lean_object* v_bs_x27_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v_v_98_ = lean_array_uget(v_bs_96_, v_i_95_);
v___x_99_ = lean_unsigned_to_nat(0u);
v_bs_x27_100_ = lean_array_uset(v_bs_96_, v_i_95_, v___x_99_);
lean_inc(v_v_98_);
v___x_101_ = l_Lake_BinderSyntaxView_mkBinder(v_v_98_);
v___x_102_ = l_Lake_BinderSyntaxView_mkArgument(v_v_98_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_95_, v___x_104_);
v___x_106_ = lean_array_uset(v_bs_x27_100_, v_i_95_, v___x_103_);
v_i_95_ = v___x_105_;
v_bs_96_ = v___x_106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0___boxed(lean_object* v_sz_108_, lean_object* v_i_109_, lean_object* v_bs_110_){
_start:
{
size_t v_sz_boxed_111_; size_t v_i_boxed_112_; lean_object* v_res_113_; 
v_sz_boxed_111_ = lean_unbox_usize(v_sz_108_);
lean_dec(v_sz_108_);
v_i_boxed_112_ = lean_unbox_usize(v_i_109_);
lean_dec(v_i_109_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_boxed_111_, v_i_boxed_112_, v_bs_110_);
return v_res_113_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3));
v___x_124_ = l_String_toRawSubstring_x27(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16));
v___x_134_ = l_String_toRawSubstring_x27(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26));
v___x_147_ = l_String_toRawSubstring_x27(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Array_mkArray0(lean_box(0));
return v___x_170_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56));
v___x_217_ = l_String_toRawSubstring_x27(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(lean_object* v_x_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lake_nonemptyTypeCmd___closed__2));
lean_inc(v_x_237_);
v___x_241_ = l_Lean_Syntax_isOfKind(v_x_237_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_x_237_);
v___x_242_ = lean_box(1);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_a_239_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_id_249_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; size_t v___y_414_; lean_object* v___y_415_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; size_t v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_bs_509_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_549_; lean_object* v___x_560_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Lean_Syntax_getArg(v_x_237_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = l_Lean_Syntax_getArg(v_x_237_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(3u);
v_id_249_ = l_Lean_Syntax_getArg(v_x_237_, v___x_248_);
v___x_507_ = lean_unsigned_to_nat(4u);
v___x_508_ = l_Lean_Syntax_getArg(v_x_237_, v___x_507_);
lean_dec(v_x_237_);
v_bs_509_ = l_Lean_Syntax_getArgs(v___x_508_);
lean_dec(v___x_508_);
v___x_560_ = l_Lean_Syntax_getOptional_x3f(v___x_247_);
lean_dec(v___x_247_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
v___y_549_ = v___x_561_;
goto v___jp_548_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_560_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_dec(v___x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_val_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_549_ = v___x_567_;
goto v___jp_548_;
}
}
}
v___jp_250_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_280_ = l_Array_append___redArg(v___y_256_, v___y_279_);
lean_dec_ref(v___y_279_);
lean_inc_n(v___y_260_, 5);
lean_inc_n(v___y_262_, 38);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___y_262_);
lean_ctor_set(v___x_281_, 1, v___y_260_);
lean_ctor_set(v___x_281_, 2, v___x_280_);
lean_inc_ref(v___x_281_);
lean_inc_n(v___y_251_, 24);
lean_inc(v___y_259_);
v___x_282_ = l_Lean_Syntax_node7(v___y_262_, v___y_259_, v___y_271_, v___y_251_, v___x_281_, v___y_251_, v___y_251_, v___y_251_, v___y_251_);
v___x_283_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0));
lean_inc_ref_n(v___y_252_, 4);
lean_inc_ref_n(v___y_276_, 13);
lean_inc_ref_n(v___y_258_, 13);
v___x_284_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_252_, v___x_283_);
v___x_285_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_262_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc(v_id_249_);
v___x_287_ = lean_array_push(v___y_267_, v_id_249_);
v___x_288_ = lean_array_push(v___x_287_, v___y_268_);
lean_inc_n(v___y_278_, 2);
lean_inc(v___y_261_);
v___x_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_289_, 0, v___y_261_);
lean_ctor_set(v___x_289_, 1, v___y_278_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
v___x_290_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2));
v___x_291_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_252_, v___x_290_);
v___x_292_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3));
lean_inc_ref_n(v___y_263_, 5);
v___x_293_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_263_, v___x_292_);
v___x_294_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4));
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v___y_262_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_Syntax_node2(v___y_262_, v___x_293_, v___x_295_, v___y_251_);
lean_inc(v___y_254_);
lean_inc(v___y_270_);
v___x_297_ = l_Lean_Syntax_node2(v___y_262_, v___y_270_, v___y_254_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node1(v___y_262_, v___y_260_, v___x_297_);
v___x_299_ = l_Lean_Syntax_node2(v___y_262_, v___x_291_, v___y_255_, v___x_298_);
v___x_300_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5));
v___x_301_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_252_, v___x_300_);
v___x_302_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6));
v___x_303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_303_, 0, v___y_262_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7));
v___x_305_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_263_, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8));
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_262_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9);
v___x_309_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10));
lean_inc_n(v___y_275_, 2);
lean_inc_n(v___y_265_, 2);
v___x_310_ = l_Lean_addMacroScope(v___y_265_, v___x_309_, v___y_275_);
lean_inc_n(v___y_264_, 3);
v___x_311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_311_, 0, v___y_262_);
lean_ctor_set(v___x_311_, 1, v___x_308_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___y_264_);
lean_inc_ref(v___x_307_);
lean_inc(v___y_266_);
lean_inc(v___x_305_);
v___x_312_ = l_Lean_Syntax_node5(v___y_262_, v___x_305_, v___y_266_, v___x_307_, v___x_311_, v___y_251_, v___y_251_);
v___x_313_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11));
v___x_314_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12));
v___x_315_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___x_313_, v___x_314_);
v___x_316_ = l_Lean_Syntax_node2(v___y_262_, v___x_315_, v___y_251_, v___y_251_);
lean_inc(v___x_316_);
lean_inc_ref(v___x_303_);
lean_inc(v___x_301_);
v___x_317_ = l_Lean_Syntax_node4(v___y_262_, v___x_301_, v___x_303_, v___x_312_, v___x_316_, v___y_251_);
v___x_318_ = l_Lean_Syntax_node5(v___y_262_, v___x_284_, v___x_286_, v___x_289_, v___x_299_, v___x_317_, v___y_251_);
lean_inc(v___y_253_);
v___x_319_ = l_Lean_Syntax_node2(v___y_262_, v___y_253_, v___x_282_, v___x_318_);
v___x_320_ = l_Lean_Syntax_node7(v___y_262_, v___y_259_, v___y_251_, v___y_251_, v___x_281_, v___y_251_, v___y_251_, v___y_251_, v___y_251_);
v___x_321_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13));
v___x_322_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_252_, v___x_321_);
v___x_323_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14));
v___x_324_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_263_, v___x_323_);
v___x_325_ = l_Lean_Syntax_node1(v___y_262_, v___x_324_, v___y_251_);
v___x_326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_326_, 0, v___y_262_);
lean_ctor_set(v___x_326_, 1, v___x_321_);
v___x_327_ = l_Lean_Syntax_node2(v___y_262_, v___y_278_, v___y_269_, v___y_251_);
v___x_328_ = l_Lean_Syntax_node1(v___y_262_, v___y_260_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15));
v___x_330_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_263_, v___x_329_);
v___x_331_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17);
v___x_332_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18));
v___x_333_ = l_Lean_addMacroScope(v___y_265_, v___x_332_, v___y_275_);
lean_inc(v___y_273_);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___y_273_);
v___x_335_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19));
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___y_264_);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_338_, 0, v___y_262_);
lean_ctor_set(v___x_338_, 1, v___x_331_);
lean_ctor_set(v___x_338_, 2, v___x_333_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
v___x_339_ = l_Lean_Syntax_mkApp(v_id_249_, v___y_274_);
v___x_340_ = l_Lean_Syntax_node1(v___y_262_, v___y_260_, v___x_339_);
v___x_341_ = l_Lean_Syntax_node2(v___y_262_, v___x_330_, v___x_338_, v___x_340_);
v___x_342_ = l_Lean_Syntax_node2(v___y_262_, v___y_270_, v___y_254_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node2(v___y_262_, v___y_277_, v___y_251_, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20));
v___x_345_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___y_263_, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21));
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_262_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22));
v___x_349_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23));
v___x_350_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___x_348_, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24));
v___x_352_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___x_348_, v___x_351_);
v___x_353_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25));
v___x_354_ = l_Lean_Name_mkStr4(v___y_258_, v___y_276_, v___x_348_, v___x_353_);
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v___y_262_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
v___x_356_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27);
v___x_357_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28));
v___x_358_ = l_Lean_addMacroScope(v___y_265_, v___x_357_, v___y_275_);
v___x_359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_359_, 0, v___y_262_);
lean_ctor_set(v___x_359_, 1, v___x_356_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_ctor_set(v___x_359_, 3, v___y_264_);
v___x_360_ = l_Lean_Syntax_node5(v___y_262_, v___x_305_, v___y_266_, v___x_307_, v___x_359_, v___y_251_, v___y_251_);
v___x_361_ = l_Lean_Syntax_node2(v___y_262_, v___x_354_, v___x_355_, v___x_360_);
v___x_362_ = l_Lean_Syntax_node1(v___y_262_, v___y_260_, v___x_361_);
v___x_363_ = l_Lean_Syntax_node1(v___y_262_, v___x_352_, v___x_362_);
v___x_364_ = l_Lean_Syntax_node1(v___y_262_, v___x_350_, v___x_363_);
v___x_365_ = l_Lean_Syntax_node2(v___y_262_, v___x_345_, v___x_347_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node4(v___y_262_, v___x_301_, v___x_303_, v___x_365_, v___x_316_, v___y_251_);
v___x_367_ = l_Lean_Syntax_node6(v___y_262_, v___x_322_, v___x_325_, v___x_326_, v___y_251_, v___x_328_, v___x_343_, v___x_366_);
v___x_368_ = l_Lean_Syntax_node2(v___y_262_, v___y_253_, v___x_320_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node3(v___y_262_, v___y_260_, v___y_257_, v___x_319_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___y_272_);
return v___x_370_;
}
v___jp_371_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_inc_ref(v___y_377_);
v___x_401_ = l_Array_append___redArg(v___y_377_, v___y_400_);
lean_dec_ref(v___y_400_);
lean_inc(v___y_381_);
lean_inc(v___y_383_);
v___x_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_402_, 0, v___y_383_);
lean_ctor_set(v___x_402_, 1, v___y_381_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
if (lean_obj_tag(v___y_387_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_404_; 
v_val_403_ = lean_ctor_get(v___y_387_, 0);
lean_inc(v_val_403_);
lean_dec_ref(v___y_387_);
v___x_404_ = l_Array_mkArray1___redArg(v_val_403_);
v___y_251_ = v___y_372_;
v___y_252_ = v___y_374_;
v___y_253_ = v___y_373_;
v___y_254_ = v___y_375_;
v___y_255_ = v___y_376_;
v___y_256_ = v___y_377_;
v___y_257_ = v___y_379_;
v___y_258_ = v___y_378_;
v___y_259_ = v___y_380_;
v___y_260_ = v___y_381_;
v___y_261_ = v___y_382_;
v___y_262_ = v___y_383_;
v___y_263_ = v___y_384_;
v___y_264_ = v___y_385_;
v___y_265_ = v___y_386_;
v___y_266_ = v___y_388_;
v___y_267_ = v___y_389_;
v___y_268_ = v___y_390_;
v___y_269_ = v___y_391_;
v___y_270_ = v___y_392_;
v___y_271_ = v___x_402_;
v___y_272_ = v___y_393_;
v___y_273_ = v___y_394_;
v___y_274_ = v___y_395_;
v___y_275_ = v___y_396_;
v___y_276_ = v___y_397_;
v___y_277_ = v___y_398_;
v___y_278_ = v___y_399_;
v___y_279_ = v___x_404_;
goto v___jp_250_;
}
else
{
lean_object* v___x_405_; 
lean_dec(v___y_387_);
v___x_405_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29));
v___y_251_ = v___y_372_;
v___y_252_ = v___y_374_;
v___y_253_ = v___y_373_;
v___y_254_ = v___y_375_;
v___y_255_ = v___y_376_;
v___y_256_ = v___y_377_;
v___y_257_ = v___y_379_;
v___y_258_ = v___y_378_;
v___y_259_ = v___y_380_;
v___y_260_ = v___y_381_;
v___y_261_ = v___y_382_;
v___y_262_ = v___y_383_;
v___y_263_ = v___y_384_;
v___y_264_ = v___y_385_;
v___y_265_ = v___y_386_;
v___y_266_ = v___y_388_;
v___y_267_ = v___y_389_;
v___y_268_ = v___y_390_;
v___y_269_ = v___y_391_;
v___y_270_ = v___y_392_;
v___y_271_ = v___x_402_;
v___y_272_ = v___y_393_;
v___y_273_ = v___y_394_;
v___y_274_ = v___y_395_;
v___y_275_ = v___y_396_;
v___y_276_ = v___y_397_;
v___y_277_ = v___y_398_;
v___y_278_ = v___y_399_;
v___y_279_ = v___x_405_;
goto v___jp_250_;
}
}
v___jp_406_:
{
lean_object* v_quotContext_416_; lean_object* v_currMacroScope_417_; lean_object* v_ref_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; size_t v_sz_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_quotContext_416_ = lean_ctor_get(v_a_238_, 1);
v_currMacroScope_417_ = lean_ctor_get(v_a_238_, 2);
v_ref_418_ = lean_ctor_get(v_a_238_, 5);
v___x_419_ = l_Lean_mkIdentFrom(v_id_249_, v___y_415_, v___y_408_);
lean_inc_ref(v___y_411_);
lean_inc(v___y_412_);
v___x_420_ = l_Lean_Syntax_mkApp(v___y_412_, v___y_411_);
v___x_421_ = l_Lean_SourceInfo_fromRef(v_ref_418_, v___y_408_);
v___x_422_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31));
v___x_423_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32));
v___x_424_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33));
v___x_425_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34));
v___x_426_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36));
v___x_427_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38));
v___x_428_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
lean_inc_n(v___x_421_, 19);
v___x_429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_421_);
lean_ctor_set(v___x_429_, 1, v___x_422_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
v___x_430_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40));
v___x_431_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41));
v___x_432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_421_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
v___x_433_ = l_Lean_Syntax_node1(v___x_421_, v___x_431_, v___x_432_);
v___x_434_ = l_Lean_Syntax_node1(v___x_421_, v___x_422_, v___x_433_);
lean_inc_ref_n(v___x_429_, 7);
v___x_435_ = l_Lean_Syntax_node7(v___x_421_, v___x_427_, v___x_429_, v___x_429_, v___x_434_, v___x_429_, v___x_429_, v___x_429_, v___x_429_);
v___x_436_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42));
v___x_437_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43));
v___x_438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_421_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
v___x_439_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45));
v___x_440_ = lean_box(2);
v___x_441_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47));
v___x_442_ = lean_unsigned_to_nat(2u);
v___x_443_ = lean_mk_empty_array_with_capacity(v___x_442_);
lean_inc_ref(v___x_443_);
v___x_444_ = lean_array_push(v___x_443_, v___y_412_);
v___x_445_ = lean_array_push(v___x_444_, v___x_441_);
v___x_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_440_);
lean_ctor_set(v___x_446_, 1, v___x_439_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49));
v_sz_448_ = lean_array_size(v___y_410_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_448_, v___y_414_, v___y_410_);
v___x_450_ = l_Array_append___redArg(v___x_428_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_421_);
lean_ctor_set(v___x_451_, 1, v___x_422_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
v___x_452_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50));
v___x_453_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52));
v___x_454_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53));
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_421_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55));
v___x_457_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57);
v___x_458_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58));
lean_inc(v_currMacroScope_417_);
lean_inc(v_quotContext_416_);
v___x_459_ = l_Lean_addMacroScope(v_quotContext_416_, v___x_458_, v_currMacroScope_417_);
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62));
v___x_462_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_462_, 0, v___x_421_);
lean_ctor_set(v___x_462_, 1, v___x_457_);
lean_ctor_set(v___x_462_, 2, v___x_459_);
lean_ctor_set(v___x_462_, 3, v___x_461_);
v___x_463_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_421_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65));
v___x_466_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66));
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_421_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Syntax_node1(v___x_421_, v___x_465_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_421_, v___x_422_, v___x_468_);
v___x_470_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67));
v___x_471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_421_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Lean_Syntax_node4(v___x_421_, v___x_456_, v___x_462_, v___x_464_, v___x_469_, v___x_471_);
lean_inc_ref(v___x_455_);
v___x_473_ = l_Lean_Syntax_node2(v___x_421_, v___x_453_, v___x_455_, v___x_472_);
lean_inc_ref(v___x_451_);
v___x_474_ = l_Lean_Syntax_node2(v___x_421_, v___x_447_, v___x_451_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node4(v___x_421_, v___x_437_, v___x_438_, v___x_446_, v___x_474_, v___x_429_);
v___x_476_ = l_Lean_Syntax_node2(v___x_421_, v___x_426_, v___x_435_, v___x_475_);
if (lean_obj_tag(v___y_413_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; 
v_val_477_ = lean_ctor_get(v___y_413_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v___y_413_);
v___x_478_ = l_Array_mkArray1___redArg(v_val_477_);
lean_inc(v_currMacroScope_417_);
lean_inc(v_quotContext_416_);
v___y_372_ = v___x_429_;
v___y_373_ = v___x_426_;
v___y_374_ = v___x_425_;
v___y_375_ = v___x_455_;
v___y_376_ = v___x_451_;
v___y_377_ = v___x_428_;
v___y_378_ = v___x_423_;
v___y_379_ = v___x_476_;
v___y_380_ = v___x_427_;
v___y_381_ = v___x_422_;
v___y_382_ = v___x_440_;
v___y_383_ = v___x_421_;
v___y_384_ = v___x_452_;
v___y_385_ = v___x_460_;
v___y_386_ = v_quotContext_416_;
v___y_387_ = v___y_407_;
v___y_388_ = v___x_420_;
v___y_389_ = v___x_443_;
v___y_390_ = v___x_441_;
v___y_391_ = v___x_419_;
v___y_392_ = v___x_453_;
v___y_393_ = v___y_409_;
v___y_394_ = v___x_460_;
v___y_395_ = v___y_411_;
v___y_396_ = v_currMacroScope_417_;
v___y_397_ = v___x_424_;
v___y_398_ = v___x_447_;
v___y_399_ = v___x_439_;
v___y_400_ = v___x_478_;
goto v___jp_371_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v___y_413_);
v___x_479_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29));
lean_inc(v_currMacroScope_417_);
lean_inc(v_quotContext_416_);
v___y_372_ = v___x_429_;
v___y_373_ = v___x_426_;
v___y_374_ = v___x_425_;
v___y_375_ = v___x_455_;
v___y_376_ = v___x_451_;
v___y_377_ = v___x_428_;
v___y_378_ = v___x_423_;
v___y_379_ = v___x_476_;
v___y_380_ = v___x_427_;
v___y_381_ = v___x_422_;
v___y_382_ = v___x_440_;
v___y_383_ = v___x_421_;
v___y_384_ = v___x_452_;
v___y_385_ = v___x_460_;
v___y_386_ = v_quotContext_416_;
v___y_387_ = v___y_407_;
v___y_388_ = v___x_420_;
v___y_389_ = v___x_443_;
v___y_390_ = v___x_441_;
v___y_391_ = v___x_419_;
v___y_392_ = v___x_453_;
v___y_393_ = v___y_409_;
v___y_394_ = v___x_460_;
v___y_395_ = v___y_411_;
v___y_396_ = v_currMacroScope_417_;
v___y_397_ = v___x_424_;
v___y_398_ = v___x_447_;
v___y_399_ = v___x_439_;
v___y_400_ = v___x_479_;
goto v___jp_371_;
}
}
v___jp_480_:
{
uint8_t v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = 0;
v___x_490_ = l_Lean_mkIdentFrom(v_id_249_, v___y_488_, v___x_489_);
v___x_491_ = l_Lean_Name_hasMacroScopes(v___y_487_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(v___y_487_);
v___y_407_ = v___y_481_;
v___y_408_ = v___x_489_;
v___y_409_ = v___y_482_;
v___y_410_ = v___y_483_;
v___y_411_ = v___y_484_;
v___y_412_ = v___x_490_;
v___y_413_ = v___y_485_;
v___y_414_ = v___y_486_;
v___y_415_ = v___x_492_;
goto v___jp_406_;
}
else
{
lean_object* v_view_493_; lean_object* v_name_494_; lean_object* v_imported_495_; lean_object* v_ctx_496_; lean_object* v_scopes_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
v_view_493_ = l_Lean_extractMacroScopes(v___y_487_);
v_name_494_ = lean_ctor_get(v_view_493_, 0);
v_imported_495_ = lean_ctor_get(v_view_493_, 1);
v_ctx_496_ = lean_ctor_get(v_view_493_, 2);
v_scopes_497_ = lean_ctor_get(v_view_493_, 3);
v_isSharedCheck_506_ = !lean_is_exclusive(v_view_493_);
if (v_isSharedCheck_506_ == 0)
{
v___x_499_ = v_view_493_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_scopes_497_);
lean_inc(v_ctx_496_);
lean_inc(v_imported_495_);
lean_inc(v_name_494_);
lean_dec(v_view_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(v_name_494_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_imported_495_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_ctx_496_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_scopes_497_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MacroScopesView_review(v___x_503_);
v___y_407_ = v___y_481_;
v___y_408_ = v___x_489_;
v___y_409_ = v___y_482_;
v___y_410_ = v___y_483_;
v___y_411_ = v___y_484_;
v___y_412_ = v___x_490_;
v___y_413_ = v___y_485_;
v___y_414_ = v___y_486_;
v___y_415_ = v___x_504_;
goto v___jp_406_;
}
}
}
}
v___jp_510_:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lake_expandBinders(v_bs_509_, v_a_238_, v_a_239_);
lean_dec_ref(v_bs_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v_a_515_; size_t v_sz_516_; size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
v_a_515_ = lean_ctor_get(v___x_513_, 1);
lean_inc(v_a_515_);
lean_dec_ref(v___x_513_);
v_sz_516_ = lean_array_size(v_a_514_);
v___x_517_ = ((size_t)0ULL);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_516_, v___x_517_, v_a_514_);
v___x_519_ = l_Array_unzip___redArg(v___x_518_);
lean_dec_ref(v___x_518_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_fst_520_);
v_snd_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v___x_519_);
v___x_522_ = l_Lean_TSyntax_getId(v_id_249_);
v___x_523_ = l_Lean_Name_hasMacroScopes(v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_inc(v___x_522_);
v___x_524_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(v___x_522_);
v___y_481_ = v___y_511_;
v___y_482_ = v_a_515_;
v___y_483_ = v_fst_520_;
v___y_484_ = v_snd_521_;
v___y_485_ = v___y_512_;
v___y_486_ = v___x_517_;
v___y_487_ = v___x_522_;
v___y_488_ = v___x_524_;
goto v___jp_480_;
}
else
{
lean_object* v_view_525_; lean_object* v_name_526_; lean_object* v_imported_527_; lean_object* v_ctx_528_; lean_object* v_scopes_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_538_; 
lean_inc(v___x_522_);
v_view_525_ = l_Lean_extractMacroScopes(v___x_522_);
v_name_526_ = lean_ctor_get(v_view_525_, 0);
v_imported_527_ = lean_ctor_get(v_view_525_, 1);
v_ctx_528_ = lean_ctor_get(v_view_525_, 2);
v_scopes_529_ = lean_ctor_get(v_view_525_, 3);
v_isSharedCheck_538_ = !lean_is_exclusive(v_view_525_);
if (v_isSharedCheck_538_ == 0)
{
v___x_531_ = v_view_525_;
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_scopes_529_);
lean_inc(v_ctx_528_);
lean_inc(v_imported_527_);
lean_inc(v_name_526_);
lean_dec(v_view_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(v_name_526_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_imported_527_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_ctx_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_scopes_529_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_MacroScopesView_review(v___x_535_);
v___y_481_ = v___y_511_;
v___y_482_ = v_a_515_;
v___y_483_ = v_fst_520_;
v___y_484_ = v_snd_521_;
v___y_485_ = v___y_512_;
v___y_486_ = v___x_517_;
v___y_487_ = v___x_522_;
v___y_488_ = v___x_536_;
goto v___jp_480_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v___y_512_);
lean_dec(v___y_511_);
lean_dec(v_id_249_);
v_a_539_ = lean_ctor_get(v___x_513_, 0);
v_a_540_ = lean_ctor_get(v___x_513_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_513_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_inc(v_a_539_);
lean_dec(v___x_513_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
v___jp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Syntax_getOptional_x3f(v___x_245_);
lean_dec(v___x_245_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
v___y_511_ = v___y_549_;
v___y_512_ = v___x_551_;
goto v___jp_510_;
}
else
{
lean_object* v_val_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_val_552_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_val_552_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_val_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_511_ = v___y_549_;
v___y_512_ = v___x_557_;
goto v___jp_510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___boxed(lean_object* v_x_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(v_x_570_, v_a_571_, v_a_572_);
lean_dec_ref(v_a_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(size_t v_sz_605_, size_t v_i_606_, lean_object* v_bs_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_608_ == 0)
{
return v_bs_607_;
}
else
{
lean_object* v_v_609_; lean_object* v___x_610_; lean_object* v_bs_x27_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v_v_609_ = lean_array_uget(v_bs_607_, v_i_606_);
v___x_610_ = lean_unsigned_to_nat(0u);
v_bs_x27_611_ = lean_array_uset(v_bs_607_, v_i_606_, v___x_610_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_606_, v___x_612_);
v___x_614_ = lean_array_uset(v_bs_x27_611_, v_i_606_, v_v_609_);
v_i_606_ = v___x_613_;
v_bs_607_ = v___x_614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0___boxed(lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_bs_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_boxed_619_, v_i_boxed_620_, v_bs_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(size_t v_sz_622_, size_t v_i_623_, lean_object* v_bs_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_625_ == 0)
{
return v_bs_624_;
}
else
{
lean_object* v_v_626_; lean_object* v___x_627_; lean_object* v_bs_x27_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v_v_626_ = lean_array_uget(v_bs_624_, v_i_623_);
v___x_627_ = lean_unsigned_to_nat(0u);
v_bs_x27_628_ = lean_array_uset(v_bs_624_, v_i_623_, v___x_627_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_623_, v___x_629_);
v___x_631_ = lean_array_uset(v_bs_x27_628_, v_i_623_, v_v_626_);
v_i_623_ = v___x_630_;
v_bs_624_ = v___x_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1___boxed(lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_bs_635_){
_start:
{
size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_sz_boxed_636_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_637_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v_sz_boxed_636_, v_i_boxed_637_, v_bs_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(lean_object* v___x_646_, lean_object* v___x_647_, size_t v_sz_648_, size_t v_i_649_, lean_object* v_bs_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_651_ == 0)
{
lean_dec(v___x_647_);
lean_dec(v___x_646_);
return v_bs_650_;
}
else
{
lean_object* v___x_652_; lean_object* v_v_653_; lean_object* v___x_654_; lean_object* v_bs_x27_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_652_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31));
v_v_653_ = lean_array_uget(v_bs_650_, v_i_649_);
v___x_654_ = lean_unsigned_to_nat(0u);
v_bs_x27_655_ = lean_array_uset(v_bs_650_, v_i_649_, v___x_654_);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1));
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2));
lean_inc_n(v___x_646_, 4);
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_646_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_Syntax_node1(v___x_646_, v___x_652_, v_v_653_);
v___x_660_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_646_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc(v___x_647_);
v___x_662_ = l_Lean_Syntax_node4(v___x_646_, v___x_656_, v___x_658_, v___x_659_, v___x_647_, v___x_661_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_add(v_i_649_, v___x_663_);
v___x_665_ = lean_array_uset(v_bs_x27_655_, v_i_649_, v___x_662_);
v_i_649_ = v___x_664_;
v_bs_650_ = v___x_665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___boxed(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v_sz_669_, lean_object* v_i_670_, lean_object* v_bs_671_){
_start:
{
size_t v_sz_boxed_672_; size_t v_i_boxed_673_; lean_object* v_res_674_; 
v_sz_boxed_672_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v_i_boxed_673_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___x_667_, v___x_668_, v_sz_boxed_672_, v_i_boxed_673_, v_bs_671_);
return v_res_674_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0));
v___x_677_ = l_String_toRawSubstring_x27(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9));
v___x_690_ = l_String_toRawSubstring_x27(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19));
v___x_703_ = l_String_toRawSubstring_x27(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23));
v___x_710_ = l_String_toRawSubstring_x27(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31(void){
_start:
{
lean_object* v___x_722_; lean_object* v_mk_723_; 
v___x_722_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30));
v_mk_723_ = lean_mk_syntax_ident(v___x_722_);
return v_mk_723_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34(void){
_start:
{
lean_object* v___x_727_; lean_object* v_unsafeMk_728_; 
v___x_727_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33));
v_unsafeMk_728_ = lean_mk_syntax_ident(v___x_727_);
return v_unsafeMk_728_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37(void){
_start:
{
lean_object* v___x_732_; lean_object* v_instCoeMk_733_; 
v___x_732_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36));
v_instCoeMk_733_ = lean_mk_syntax_ident(v___x_732_);
return v_instCoeMk_733_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40(void){
_start:
{
lean_object* v___x_737_; lean_object* v_get_738_; 
v___x_737_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39));
v_get_738_ = lean_mk_syntax_ident(v___x_737_);
return v_get_738_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43(void){
_start:
{
lean_object* v___x_742_; lean_object* v_unsafeGet_743_; 
v___x_742_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42));
v_unsafeGet_743_ = lean_mk_syntax_ident(v___x_742_);
return v_unsafeGet_743_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46(void){
_start:
{
lean_object* v___x_747_; lean_object* v_instCoeGet_748_; 
v___x_747_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45));
v_instCoeGet_748_ = lean_mk_syntax_ident(v___x_747_);
return v_instCoeGet_748_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58));
v___x_782_ = l_String_toRawSubstring_x27(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67(void){
_start:
{
lean_object* v___x_803_; lean_object* v_unsafeMk_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47));
v_unsafeMk_804_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
v___x_805_ = lean_unsigned_to_nat(2u);
v___x_806_ = lean_mk_empty_array_with_capacity(v___x_805_);
v___x_807_ = lean_array_push(v___x_806_, v_unsafeMk_804_);
v___x_808_ = lean_array_push(v___x_807_, v___x_803_);
return v___x_808_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67);
v___x_810_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45));
v___x_811_ = lean_box(2);
v___x_812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
lean_ctor_set(v___x_812_, 2, v___x_809_);
return v___x_812_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75));
v___x_837_ = l_String_toRawSubstring_x27(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81));
v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(lean_object* v_x_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lake_hydrateOpaqueTypeCmd___closed__1));
lean_inc(v_x_856_);
v___x_860_ = l_Lean_Syntax_isOfKind(v_x_856_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_x_856_);
v___x_861_ = lean_box(1);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_a_858_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_args_871_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; size_t v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; size_t v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_1083_; lean_object* v___x_1192_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Lean_Syntax_getArg(v_x_856_, v___x_863_);
v___x_865_ = lean_unsigned_to_nat(2u);
v___x_866_ = l_Lean_Syntax_getArg(v_x_856_, v___x_865_);
v___x_867_ = lean_unsigned_to_nat(3u);
v___x_868_ = l_Lean_Syntax_getArg(v_x_856_, v___x_867_);
v___x_869_ = lean_unsigned_to_nat(4u);
v___x_870_ = l_Lean_Syntax_getArg(v_x_856_, v___x_869_);
lean_dec(v_x_856_);
v_args_871_ = l_Lean_Syntax_getArgs(v___x_870_);
lean_dec(v___x_870_);
v___x_1192_ = l_Lean_Syntax_getOptional_x3f(v___x_864_);
lean_dec(v___x_864_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_box(0);
v___y_1083_ = v___x_1193_;
goto v___jp_1082_;
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_val_1194_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_val_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v___y_1083_ = v___x_1199_;
goto v___jp_1082_;
}
}
}
v___jp_872_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; size_t v_sz_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_inc_ref(v___y_896_);
v___x_925_ = l_Array_append___redArg(v___y_896_, v___y_924_);
lean_dec_ref(v___y_924_);
lean_inc_n(v___y_892_, 18);
lean_inc_n(v___y_923_, 79);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v___y_923_);
lean_ctor_set(v___x_926_, 1, v___y_892_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
lean_inc_ref_n(v___x_926_, 2);
lean_inc_n(v___y_893_, 34);
lean_inc_n(v___y_910_, 2);
v___x_927_ = l_Lean_Syntax_node7(v___y_923_, v___y_910_, v___y_893_, v___y_912_, v___x_926_, v___y_893_, v___y_893_, v___y_893_, v___y_893_);
v___x_928_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42));
lean_inc_ref_n(v___y_919_, 4);
lean_inc_ref_n(v___y_903_, 8);
lean_inc_ref_n(v___y_879_, 9);
v___x_929_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_919_, v___x_928_);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_923_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
lean_inc_n(v___y_878_, 3);
lean_inc_ref_n(v___y_883_, 2);
v___x_931_ = lean_array_push(v___y_883_, v___y_878_);
lean_inc_n(v___y_916_, 3);
v___x_932_ = lean_array_push(v___x_931_, v___y_916_);
lean_inc_n(v___y_915_, 5);
lean_inc_n(v___y_913_, 3);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v___y_913_);
lean_ctor_set(v___x_933_, 1, v___y_915_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
v___x_934_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48));
v___x_935_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_919_, v___x_934_);
lean_inc_n(v___x_935_, 4);
v___x_936_ = l_Lean_Syntax_node2(v___y_923_, v___x_935_, v___y_893_, v___y_887_);
lean_inc_ref(v___x_930_);
lean_inc(v___x_929_);
v___x_937_ = l_Lean_Syntax_node4(v___y_923_, v___x_929_, v___x_930_, v___x_933_, v___x_936_, v___y_893_);
lean_inc_n(v___y_886_, 5);
v___x_938_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___x_927_, v___x_937_);
v___x_939_ = l_Lean_Syntax_node7(v___y_923_, v___y_910_, v___y_893_, v___y_893_, v___x_926_, v___y_893_, v___y_893_, v___y_893_, v___y_893_);
v___x_940_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13));
v___x_941_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_919_, v___x_940_);
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___y_923_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_inc(v___y_920_);
v___x_943_ = l_Lean_Syntax_node2(v___y_923_, v___y_915_, v___y_920_, v___y_893_);
v___x_944_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_943_);
v___x_945_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1);
v___x_946_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2));
lean_inc_n(v___y_905_, 3);
lean_inc_n(v___y_897_, 3);
v___x_947_ = l_Lean_addMacroScope(v___y_897_, v___x_946_, v___y_905_);
lean_inc_n(v___y_885_, 3);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___y_885_);
v___x_949_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3));
lean_inc_n(v___y_877_, 4);
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___y_877_);
v___x_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_952_, 0, v___y_923_);
lean_ctor_set(v___x_952_, 1, v___x_945_);
lean_ctor_set(v___x_952_, 2, v___x_947_);
lean_ctor_set(v___x_952_, 3, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4));
lean_inc_ref_n(v___y_895_, 4);
v___x_954_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_895_, v___x_953_);
v___x_955_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5));
v___x_956_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_895_, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6));
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_923_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8));
v___x_960_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10);
v___x_961_ = lean_box(0);
v___x_962_ = l_Lean_addMacroScope(v___y_897_, v___x_961_, v___y_905_);
v___x_963_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12));
v___x_964_ = l_Lean_Name_mkStr1(v___y_879_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___y_877_);
v___x_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_963_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_968_, 0, v___y_923_);
lean_ctor_set(v___x_968_, 1, v___x_960_);
lean_ctor_set(v___x_968_, 2, v___x_962_);
lean_ctor_set(v___x_968_, 3, v___x_967_);
v___x_969_ = l_Lean_Syntax_node1(v___y_923_, v___x_959_, v___x_968_);
v___x_970_ = l_Lean_Syntax_node2(v___y_923_, v___x_956_, v___x_958_, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___y_923_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_inc_ref(v___x_972_);
lean_inc(v___y_898_);
lean_inc(v___x_970_);
lean_inc(v___x_954_);
v___x_973_ = l_Lean_Syntax_node3(v___y_923_, v___x_954_, v___x_970_, v___y_898_, v___x_972_);
lean_inc(v___y_904_);
v___x_974_ = l_Lean_Syntax_node3(v___y_923_, v___x_954_, v___x_970_, v___y_904_, v___x_972_);
lean_inc_n(v___x_974_, 2);
lean_inc_n(v___x_973_, 2);
v___x_975_ = l_Lean_Syntax_node2(v___y_923_, v___y_892_, v___x_973_, v___x_974_);
lean_inc_ref(v___x_952_);
lean_inc_n(v___y_918_, 4);
v___x_976_ = l_Lean_Syntax_node2(v___y_923_, v___y_918_, v___x_952_, v___x_975_);
lean_inc_n(v___y_882_, 3);
lean_inc_n(v___y_900_, 3);
v___x_977_ = l_Lean_Syntax_node2(v___y_923_, v___y_900_, v___y_882_, v___x_976_);
v___x_978_ = l_Lean_Syntax_node2(v___y_923_, v___x_935_, v___y_893_, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14));
v___x_980_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_895_, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15));
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___y_923_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___y_878_);
v___x_984_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___y_923_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
lean_inc_ref_n(v___x_985_, 2);
lean_inc_ref_n(v___x_982_, 2);
lean_inc_n(v___x_980_, 2);
v___x_986_ = l_Lean_Syntax_node3(v___y_923_, v___x_980_, v___x_982_, v___x_983_, v___x_985_);
lean_inc_n(v___y_901_, 2);
lean_inc_n(v___y_891_, 2);
lean_inc_n(v___y_889_, 2);
v___x_987_ = l_Lean_Syntax_node4(v___y_923_, v___y_889_, v___y_891_, v___x_986_, v___y_901_, v___y_893_);
lean_inc_ref_n(v___x_942_, 2);
lean_inc_n(v___y_921_, 3);
lean_inc_n(v___x_941_, 2);
v___x_988_ = l_Lean_Syntax_node6(v___y_923_, v___x_941_, v___y_921_, v___x_942_, v___y_893_, v___x_944_, v___x_978_, v___x_987_);
lean_inc_n(v___x_939_, 2);
v___x_989_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___x_939_, v___x_988_);
lean_inc_n(v___y_876_, 2);
v___x_990_ = lean_array_push(v___y_883_, v___y_876_);
v___x_991_ = lean_array_push(v___x_990_, v___y_916_);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___y_913_);
lean_ctor_set(v___x_992_, 1, v___y_915_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = l_Lean_Syntax_node3(v___y_923_, v___y_902_, v___y_904_, v___y_873_, v___y_898_);
v___x_994_ = l_Lean_Syntax_node2(v___y_923_, v___y_900_, v___y_882_, v___x_993_);
lean_inc(v___x_994_);
v___x_995_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_994_);
v___x_996_ = l_Lean_Syntax_node2(v___y_923_, v___y_922_, v___y_893_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node5(v___y_923_, v___y_917_, v___y_888_, v___x_992_, v___x_996_, v___y_907_, v___y_893_);
v___x_998_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___y_890_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___y_876_);
v___x_1000_ = l_Lean_Syntax_node2(v___y_923_, v___y_875_, v___y_899_, v___x_999_);
v___x_1001_ = l_Lean_Syntax_node2(v___y_923_, v___y_880_, v___y_921_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1001_);
lean_inc(v___y_874_);
v___x_1003_ = l_Lean_Syntax_node3(v___y_923_, v___y_908_, v___y_906_, v___x_1002_, v___y_874_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node7(v___y_923_, v___y_910_, v___y_893_, v___x_1004_, v___x_926_, v___y_893_, v___y_893_, v___y_893_, v___y_893_);
lean_inc_n(v___y_914_, 2);
v___x_1006_ = lean_array_push(v___y_883_, v___y_914_);
v___x_1007_ = lean_array_push(v___x_1006_, v___y_916_);
v___x_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___y_913_);
lean_ctor_set(v___x_1008_, 1, v___y_915_);
lean_ctor_set(v___x_1008_, 2, v___x_1007_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v___y_894_, v___y_909_, v_args_871_);
v_sz_1010_ = lean_array_size(v___x_1009_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___y_923_, v___y_893_, v_sz_1010_, v___y_909_, v___x_1009_);
v___x_1012_ = l_Array_append___redArg(v___y_896_, v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1013_, 0, v___y_923_);
lean_ctor_set(v___x_1013_, 1, v___y_892_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node2(v___y_923_, v___x_935_, v___x_1013_, v___x_994_);
v___x_1015_ = l_Lean_Syntax_node4(v___y_923_, v___x_929_, v___x_930_, v___x_1008_, v___x_1014_, v___y_893_);
v___x_1016_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___x_1005_, v___x_1015_);
lean_inc(v___y_911_);
v___x_1017_ = l_Lean_Syntax_node2(v___y_923_, v___y_915_, v___y_911_, v___y_893_);
v___x_1018_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node2(v___y_923_, v___y_892_, v___x_974_, v___x_973_);
v___x_1020_ = l_Lean_Syntax_node2(v___y_923_, v___y_918_, v___x_952_, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node2(v___y_923_, v___y_900_, v___y_882_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node2(v___y_923_, v___x_935_, v___y_893_, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___y_914_);
v___x_1024_ = l_Lean_Syntax_node3(v___y_923_, v___x_980_, v___x_982_, v___x_1023_, v___x_985_);
v___x_1025_ = l_Lean_Syntax_node4(v___y_923_, v___y_889_, v___y_891_, v___x_1024_, v___y_901_, v___y_893_);
v___x_1026_ = l_Lean_Syntax_node6(v___y_923_, v___x_941_, v___y_921_, v___x_942_, v___y_893_, v___x_1018_, v___x_1022_, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___x_939_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17));
v___x_1029_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_895_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18));
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___y_923_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20);
v___x_1033_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21));
v___x_1034_ = l_Lean_addMacroScope(v___y_897_, v___x_1033_, v___y_905_);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___y_885_);
v___x_1036_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22));
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___y_877_);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1039_, 0, v___y_923_);
lean_ctor_set(v___x_1039_, 1, v___x_1032_);
lean_ctor_set(v___x_1039_, 2, v___x_1034_);
lean_ctor_set(v___x_1039_, 3, v___x_1038_);
v___x_1040_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_973_);
lean_inc_ref(v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node2(v___y_923_, v___y_918_, v___x_1039_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node4(v___y_923_, v___x_1029_, v___x_1031_, v___y_893_, v___x_1041_, v___y_874_);
v___x_1043_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_974_);
v___x_1045_ = l_Lean_Syntax_node2(v___y_923_, v___y_918_, v___x_1039_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node2(v___y_923_, v___y_900_, v___y_882_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node2(v___y_923_, v___x_935_, v___x_1043_, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24);
v___x_1049_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25));
v___x_1050_ = l_Lean_addMacroScope(v___y_897_, v___x_1049_, v___y_905_);
v___x_1051_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26));
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___y_885_);
v___x_1053_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27));
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___y_877_);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1056_, 0, v___y_923_);
lean_ctor_set(v___x_1056_, 1, v___x_1048_);
lean_ctor_set(v___x_1056_, 2, v___x_1050_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
v___x_1057_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1056_);
v___x_1058_ = l_Lean_Syntax_node2(v___y_923_, v___y_918_, v___y_878_, v___x_1057_);
v___x_1059_ = l_Lean_Syntax_node1(v___y_923_, v___y_892_, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node3(v___y_923_, v___x_980_, v___x_982_, v___x_1059_, v___x_985_);
v___x_1061_ = l_Lean_Syntax_node4(v___y_923_, v___y_889_, v___y_891_, v___x_1060_, v___y_901_, v___y_893_);
v___x_1062_ = l_Lean_Syntax_node6(v___y_923_, v___x_941_, v___y_921_, v___x_942_, v___y_893_, v___y_893_, v___x_1047_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node2(v___y_923_, v___y_886_, v___x_939_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28));
v___x_1065_ = l_Lean_Name_mkStr4(v___y_879_, v___y_903_, v___y_919_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___y_923_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
v___x_1067_ = l_Lean_Syntax_node2(v___y_923_, v___y_892_, v___x_866_, v___y_893_);
v___x_1068_ = l_Lean_Syntax_node2(v___y_923_, v___x_1065_, v___x_1066_, v___x_1067_);
v___x_1069_ = lean_unsigned_to_nat(9u);
v___x_1070_ = lean_mk_empty_array_with_capacity(v___x_1069_);
v___x_1071_ = lean_array_push(v___x_1070_, v___y_884_);
v___x_1072_ = lean_array_push(v___x_1071_, v___y_881_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_938_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_989_);
v___x_1075_ = lean_array_push(v___x_1074_, v___x_998_);
v___x_1076_ = lean_array_push(v___x_1075_, v___x_1016_);
v___x_1077_ = lean_array_push(v___x_1076_, v___x_1027_);
v___x_1078_ = lean_array_push(v___x_1077_, v___x_1063_);
v___x_1079_ = lean_array_push(v___x_1078_, v___x_1068_);
v___x_1080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1080_, 0, v___y_923_);
lean_ctor_set(v___x_1080_, 1, v___y_892_);
lean_ctor_set(v___x_1080_, 2, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_a_858_);
return v___x_1081_;
}
v___jp_1082_:
{
lean_object* v_quotContext_1084_; lean_object* v_currMacroScope_1085_; lean_object* v_ref_1086_; lean_object* v_mk_1087_; lean_object* v_unsafeMk_1088_; lean_object* v_instCoeMk_1089_; lean_object* v_get_1090_; lean_object* v_unsafeGet_1091_; lean_object* v_instCoeGet_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_quotContext_1084_ = lean_ctor_get(v_a_857_, 1);
v_currMacroScope_1085_ = lean_ctor_get(v_a_857_, 2);
v_ref_1086_ = lean_ctor_get(v_a_857_, 5);
v_mk_1087_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31);
v_unsafeMk_1088_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
v_instCoeMk_1089_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37);
v_get_1090_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40);
v_unsafeGet_1091_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43);
v_instCoeGet_1092_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_SourceInfo_fromRef(v_ref_1086_, v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31));
v___x_1096_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32));
v___x_1097_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33));
v___x_1098_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34));
v___x_1099_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47));
v___x_1100_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48));
lean_inc_n(v___x_1094_, 42);
v___x_1101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1094_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_inc_n(v___x_866_, 2);
v___x_1102_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1100_, v___x_1101_, v___x_866_);
v___x_1103_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36));
v___x_1104_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38));
v___x_1105_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1094_);
lean_ctor_set(v___x_1106_, 1, v___x_1095_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50));
v___x_1108_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50));
v___x_1109_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51));
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1094_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53));
v___x_1112_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54));
lean_inc_ref_n(v___x_1106_, 11);
v___x_1113_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1112_, v___x_1106_);
v___x_1114_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57));
v___x_1115_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59);
v___x_1116_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60));
lean_inc_n(v_currMacroScope_1085_, 3);
lean_inc_n(v_quotContext_1084_, 3);
v___x_1117_ = l_Lean_addMacroScope(v_quotContext_1084_, v___x_1116_, v_currMacroScope_1085_);
v___x_1118_ = lean_box(0);
v___x_1119_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62));
v___x_1120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1094_);
lean_ctor_set(v___x_1120_, 1, v___x_1115_);
lean_ctor_set(v___x_1120_, 2, v___x_1117_);
lean_ctor_set(v___x_1120_, 3, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1114_, v___x_1120_, v___x_1106_);
lean_inc_n(v___x_1113_, 2);
v___x_1122_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1111_, v___x_1113_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63));
v___x_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1094_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_inc_ref_n(v___x_1125_, 2);
lean_inc_ref_n(v___x_1110_, 2);
v___x_1126_ = l_Lean_Syntax_node3(v___x_1094_, v___x_1108_, v___x_1110_, v___x_1123_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40));
v___x_1129_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1094_);
lean_ctor_set(v___x_1130_, 1, v___x_1128_);
v___x_1131_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1129_, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64));
v___x_1134_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65));
v___x_1135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1094_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
v___x_1136_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1134_, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1136_);
v___x_1138_ = l_Lean_Syntax_node7(v___x_1094_, v___x_1104_, v___x_1106_, v___x_1127_, v___x_1132_, v___x_1106_, v___x_1106_, v___x_1137_, v___x_1106_);
v___x_1139_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66));
v___x_1140_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1));
v___x_1141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1094_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45));
v___x_1143_ = lean_box(2);
v___x_1144_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47));
v___x_1145_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_1146_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68);
v___x_1147_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69));
v___x_1148_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52));
v___x_1149_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53));
v___x_1150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1094_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71));
v___x_1152_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72));
v_sz_1153_ = lean_array_size(v_args_871_);
v___x_1154_ = ((size_t)0ULL);
lean_inc_ref(v_args_871_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_1153_, v___x_1154_, v_args_871_);
v___x_1156_ = l_Array_append___redArg(v___x_1105_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1094_);
lean_ctor_set(v___x_1157_, 1, v___x_1095_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_inc_ref(v___x_1157_);
v___x_1158_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1152_, v___x_868_, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73));
v___x_1160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1094_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1152_, v___x_866_, v___x_1157_);
lean_inc(v___x_1161_);
lean_inc_ref(v___x_1160_);
lean_inc(v___x_1158_);
v___x_1162_ = l_Lean_Syntax_node3(v___x_1094_, v___x_1151_, v___x_1158_, v___x_1160_, v___x_1161_);
lean_inc_ref(v___x_1150_);
v___x_1163_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1148_, v___x_1150_, v___x_1162_);
lean_inc(v___x_1163_);
v___x_1164_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1163_);
v___x_1165_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1147_, v___x_1106_, v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74));
v___x_1167_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6));
v___x_1168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1094_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76);
v___x_1170_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77));
v___x_1171_ = l_Lean_addMacroScope(v_quotContext_1084_, v___x_1170_, v_currMacroScope_1085_);
v___x_1172_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79));
v___x_1173_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1094_);
lean_ctor_set(v___x_1173_, 1, v___x_1169_);
lean_ctor_set(v___x_1173_, 2, v___x_1171_);
lean_ctor_set(v___x_1173_, 3, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80));
v___x_1175_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1174_, v___x_1106_, v___x_1106_);
lean_inc(v___x_1175_);
lean_inc_ref(v___x_1168_);
v___x_1176_ = l_Lean_Syntax_node4(v___x_1094_, v___x_1166_, v___x_1168_, v___x_1173_, v___x_1175_, v___x_1106_);
lean_inc(v___x_1176_);
lean_inc_ref(v___x_1141_);
v___x_1177_ = l_Lean_Syntax_node5(v___x_1094_, v___x_1139_, v___x_1141_, v___x_1146_, v___x_1165_, v___x_1176_, v___x_1106_);
lean_inc(v___x_1138_);
v___x_1178_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1103_, v___x_1138_, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82, &l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once, _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82);
v___x_1180_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83));
v___x_1181_ = l_Lean_addMacroScope(v_quotContext_1084_, v___x_1180_, v_currMacroScope_1085_);
v___x_1182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1094_);
lean_ctor_set(v___x_1182_, 1, v___x_1179_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
lean_ctor_set(v___x_1182_, 3, v___x_1118_);
v___x_1183_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v_unsafeMk_1088_);
lean_inc_ref(v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1114_, v___x_1182_, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_node2(v___x_1094_, v___x_1111_, v___x_1113_, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_node3(v___x_1094_, v___x_1108_, v___x_1110_, v___x_1186_, v___x_1125_);
v___x_1188_ = l_Lean_Syntax_node1(v___x_1094_, v___x_1095_, v___x_1187_);
if (lean_obj_tag(v___y_1083_) == 1)
{
lean_object* v_val_1189_; lean_object* v___x_1190_; 
v_val_1189_ = lean_ctor_get(v___y_1083_, 0);
lean_inc(v_val_1189_);
lean_dec_ref(v___y_1083_);
v___x_1190_ = l_Array_mkArray1___redArg(v_val_1189_);
lean_inc(v_currMacroScope_1085_);
lean_inc(v_quotContext_1084_);
v___y_873_ = v___x_1160_;
v___y_874_ = v___x_1125_;
v___y_875_ = v___x_1114_;
v___y_876_ = v_unsafeGet_1091_;
v___y_877_ = v___x_1118_;
v___y_878_ = v_mk_1087_;
v___y_879_ = v___x_1096_;
v___y_880_ = v___x_1111_;
v___y_881_ = v___x_1178_;
v___y_882_ = v___x_1150_;
v___y_883_ = v___x_1145_;
v___y_884_ = v___x_1102_;
v___y_885_ = v___x_1118_;
v___y_886_ = v___x_1103_;
v___y_887_ = v___x_1163_;
v___y_888_ = v___x_1141_;
v___y_889_ = v___x_1166_;
v___y_890_ = v___x_1138_;
v___y_891_ = v___x_1168_;
v___y_892_ = v___x_1095_;
v___y_893_ = v___x_1106_;
v___y_894_ = v_sz_1153_;
v___y_895_ = v___x_1107_;
v___y_896_ = v___x_1105_;
v___y_897_ = v_quotContext_1084_;
v___y_898_ = v___x_1158_;
v___y_899_ = v___x_1182_;
v___y_900_ = v___x_1148_;
v___y_901_ = v___x_1175_;
v___y_902_ = v___x_1151_;
v___y_903_ = v___x_1097_;
v___y_904_ = v___x_1161_;
v___y_905_ = v_currMacroScope_1085_;
v___y_906_ = v___x_1110_;
v___y_907_ = v___x_1176_;
v___y_908_ = v___x_1108_;
v___y_909_ = v___x_1154_;
v___y_910_ = v___x_1104_;
v___y_911_ = v_instCoeGet_1092_;
v___y_912_ = v___x_1188_;
v___y_913_ = v___x_1143_;
v___y_914_ = v_get_1090_;
v___y_915_ = v___x_1142_;
v___y_916_ = v___x_1144_;
v___y_917_ = v___x_1139_;
v___y_918_ = v___x_1152_;
v___y_919_ = v___x_1098_;
v___y_920_ = v_instCoeMk_1089_;
v___y_921_ = v___x_1113_;
v___y_922_ = v___x_1147_;
v___y_923_ = v___x_1094_;
v___y_924_ = v___x_1190_;
goto v___jp_872_;
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___y_1083_);
v___x_1191_ = ((lean_object*)(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29));
lean_inc(v_currMacroScope_1085_);
lean_inc(v_quotContext_1084_);
v___y_873_ = v___x_1160_;
v___y_874_ = v___x_1125_;
v___y_875_ = v___x_1114_;
v___y_876_ = v_unsafeGet_1091_;
v___y_877_ = v___x_1118_;
v___y_878_ = v_mk_1087_;
v___y_879_ = v___x_1096_;
v___y_880_ = v___x_1111_;
v___y_881_ = v___x_1178_;
v___y_882_ = v___x_1150_;
v___y_883_ = v___x_1145_;
v___y_884_ = v___x_1102_;
v___y_885_ = v___x_1118_;
v___y_886_ = v___x_1103_;
v___y_887_ = v___x_1163_;
v___y_888_ = v___x_1141_;
v___y_889_ = v___x_1166_;
v___y_890_ = v___x_1138_;
v___y_891_ = v___x_1168_;
v___y_892_ = v___x_1095_;
v___y_893_ = v___x_1106_;
v___y_894_ = v_sz_1153_;
v___y_895_ = v___x_1107_;
v___y_896_ = v___x_1105_;
v___y_897_ = v_quotContext_1084_;
v___y_898_ = v___x_1158_;
v___y_899_ = v___x_1182_;
v___y_900_ = v___x_1148_;
v___y_901_ = v___x_1175_;
v___y_902_ = v___x_1151_;
v___y_903_ = v___x_1097_;
v___y_904_ = v___x_1161_;
v___y_905_ = v_currMacroScope_1085_;
v___y_906_ = v___x_1110_;
v___y_907_ = v___x_1176_;
v___y_908_ = v___x_1108_;
v___y_909_ = v___x_1154_;
v___y_910_ = v___x_1104_;
v___y_911_ = v_instCoeGet_1092_;
v___y_912_ = v___x_1188_;
v___y_913_ = v___x_1143_;
v___y_914_ = v_get_1090_;
v___y_915_ = v___x_1142_;
v___y_916_ = v___x_1144_;
v___y_917_ = v___x_1139_;
v___y_918_ = v___x_1152_;
v___y_919_ = v___x_1098_;
v___y_920_ = v_instCoeMk_1089_;
v___y_921_ = v___x_1113_;
v___y_922_ = v___x_1147_;
v___y_923_ = v___x_1094_;
v___y_924_ = v___x_1191_;
goto v___jp_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___boxed(lean_object* v_x_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(v_x_1202_, v_a_1203_, v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1205_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_OpaqueType(builtin);
}
#ifdef __cplusplus
}
#endif
