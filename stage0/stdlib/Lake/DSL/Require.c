// Lean compiler output
// Module: Lake.DSL.Require
// Imports: public import Lake.DSL.Syntax import Lake.Config.Dependency
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "DependencySrc.git"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DependencySrc"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 123, 123, 148, 32, 75, 229, 138)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(67, 37, 72, 153, 12, 75, 97, 98)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed from syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 110, 100, 210, 231, 203, 62, 196)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "src\?"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value),LEAN_SCALAR_PTR_LITERAL(34, 19, 24, 60, 150, 139, 215, 235)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "opts"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value),LEAN_SCALAR_PTR_LITERAL(49, 15, 216, 57, 127, 228, 200, 93)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value),LEAN_SCALAR_PTR_LITERAL(55, 11, 239, 15, 0, 67, 249, 1)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ill-formed require syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "package_dep"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value),LEAN_SCALAR_PTR_LITERAL(237, 25, 56, 91, 184, 179, 188, 66)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_value;
static const lean_array_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dependency"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value),LEAN_SCALAR_PTR_LITERAL(248, 114, 43, 207, 103, 109, 40, 59)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value;
static const lean_array_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value),LEAN_SCALAR_PTR_LITERAL(5, 204, 227, 250, 63, 151, 124, 47)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ill-formed version syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\"git#\""};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed name syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depName"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value),LEAN_SCALAR_PTR_LITERAL(11, 76, 0, 7, 47, 106, 167, 185)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromSource"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 246, 101, 8, 76, 68, 147)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fromGit"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value),LEAN_SCALAR_PTR_LITERAL(58, 198, 35, 138, 239, 183, 90, 121)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromPath"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value),LEAN_SCALAR_PTR_LITERAL(88, 231, 238, 12, 211, 124, 7, 152)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DependencySrc.path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 123, 123, 148, 32, 75, 229, 138)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value),LEAN_SCALAR_PTR_LITERAL(41, 247, 255, 238, 70, 62, 187, 2)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(203, 149, 114, 196, 65, 131, 70, 23)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value),LEAN_SCALAR_PTR_LITERAL(157, 188, 245, 236, 72, 147, 33, 123)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "withClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value),LEAN_SCALAR_PTR_LITERAL(62, 242, 50, 31, 135, 230, 200, 221)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value),LEAN_SCALAR_PTR_LITERAL(108, 123, 128, 15, 141, 170, 246, 11)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "verClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 66, 152, 98, 148, 165, 231)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "requireDecl"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 86, 225, 163, 119, 172, 216, 31)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed require declaration"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Require"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 32, 139, 116, 35, 151, 53, 69)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(239, 234, 19, 137, 104, 82, 181, 131)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(51, 249, 219, 73, 145, 150, 211, 12)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(28, 30, 72, 164, 69, 128, 229, 208)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "expandRequireDecl"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(98, 125, 241, 182, 123, 78, 83, 34)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____do__lift_2_){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = 0;
v___x_4_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2_, v___x_3_);
v___x_5_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed(lean_object* v_toPure_6_, lean_object* v_____do__lift_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(v_toPure_6_, v_____do__lift_7_);
lean_dec(v_____do__lift_7_);
return v_res_8_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5));
v___x_20_ = l_String_toRawSubstring_x27(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1(lean_object* v_scp_36_, lean_object* v_info_37_, lean_object* v_val_38_, lean_object* v_toPure_39_, lean_object* v_quotCtx_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_41_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_42_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_43_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
v___x_44_ = l_Lean_addMacroScope(v_quotCtx_40_, v___x_43_, v_scp_36_);
v___x_45_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v_info_37_);
v___x_46_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_46_, 0, v_info_37_);
lean_ctor_set(v___x_46_, 1, v___x_42_);
lean_ctor_set(v___x_46_, 2, v___x_44_);
lean_ctor_set(v___x_46_, 3, v___x_45_);
v___x_47_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v_info_37_);
v___x_48_ = l_Lean_Syntax_node1(v_info_37_, v___x_47_, v_val_38_);
v___x_49_ = l_Lean_Syntax_node2(v_info_37_, v___x_41_, v___x_46_, v___x_48_);
v___x_50_ = lean_apply_2(v_toPure_39_, lean_box(0), v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2(lean_object* v_info_51_, lean_object* v_val_52_, lean_object* v_toPure_53_, lean_object* v_toBind_54_, lean_object* v_getContext_55_, lean_object* v_scp_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_57_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1), 5, 4);
lean_closure_set(v___f_57_, 0, v_scp_56_);
lean_closure_set(v___f_57_, 1, v_info_51_);
lean_closure_set(v___f_57_, 2, v_val_52_);
lean_closure_set(v___f_57_, 3, v_toPure_53_);
v___x_58_ = lean_apply_4(v_toBind_54_, lean_box(0), lean_box(0), v_getContext_55_, v___f_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3(lean_object* v_val_59_, lean_object* v_toPure_60_, lean_object* v_toBind_61_, lean_object* v_getContext_62_, lean_object* v_getCurrMacroScope_63_, lean_object* v_info_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; 
lean_inc(v_toBind_61_);
v___f_65_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2), 6, 5);
lean_closure_set(v___f_65_, 0, v_info_64_);
lean_closure_set(v___f_65_, 1, v_val_59_);
lean_closure_set(v___f_65_, 2, v_toPure_60_);
lean_closure_set(v___f_65_, 3, v_toBind_61_);
lean_closure_set(v___f_65_, 4, v_getContext_62_);
v___x_66_ = lean_apply_4(v_toBind_61_, lean_box(0), lean_box(0), v_getCurrMacroScope_63_, v___f_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(lean_object* v_val_67_, lean_object* v_withRef_68_, lean_object* v___x_69_, lean_object* v_oldRef_70_){
_start:
{
lean_object* v_ref_71_; lean_object* v___x_72_; 
v_ref_71_ = l_Lean_replaceRef(v_val_67_, v_oldRef_70_);
v___x_72_ = lean_apply_3(v_withRef_68_, lean_box(0), v_ref_71_, v___x_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed(lean_object* v_val_73_, lean_object* v_withRef_74_, lean_object* v___x_75_, lean_object* v_oldRef_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(v_val_73_, v_withRef_74_, v___x_75_, v_oldRef_76_);
lean_dec(v_oldRef_76_);
lean_dec(v_val_73_);
return v_res_77_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0));
v___x_80_ = l_String_toRawSubstring_x27(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6(lean_object* v_scp_92_, lean_object* v_info_93_, lean_object* v_toPure_94_, lean_object* v_quotCtx_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_97_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
v___x_98_ = l_Lean_addMacroScope(v_quotCtx_95_, v___x_97_, v_scp_92_);
v___x_99_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_100_, 0, v_info_93_);
lean_ctor_set(v___x_100_, 1, v___x_96_);
lean_ctor_set(v___x_100_, 2, v___x_98_);
lean_ctor_set(v___x_100_, 3, v___x_99_);
v___x_101_ = lean_apply_2(v_toPure_94_, lean_box(0), v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5(lean_object* v_info_102_, lean_object* v_toPure_103_, lean_object* v_toBind_104_, lean_object* v_getContext_105_, lean_object* v_scp_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_107_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6), 4, 3);
lean_closure_set(v___f_107_, 0, v_scp_106_);
lean_closure_set(v___f_107_, 1, v_info_102_);
lean_closure_set(v___f_107_, 2, v_toPure_103_);
v___x_108_ = lean_apply_4(v_toBind_104_, lean_box(0), lean_box(0), v_getContext_105_, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(lean_object* v_toPure_109_, lean_object* v_toBind_110_, lean_object* v_getContext_111_, lean_object* v_getCurrMacroScope_112_, lean_object* v_info_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; 
lean_inc(v_toBind_110_);
v___f_114_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5), 5, 4);
lean_closure_set(v___f_114_, 0, v_info_113_);
lean_closure_set(v___f_114_, 1, v_toPure_109_);
lean_closure_set(v___f_114_, 2, v_toBind_110_);
lean_closure_set(v___f_114_, 3, v_getContext_111_);
v___x_115_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v_getCurrMacroScope_112_, v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_term_x3f_118_){
_start:
{
lean_object* v_toApplicative_119_; 
v_toApplicative_119_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_119_);
if (lean_obj_tag(v_term_x3f_118_) == 1)
{
lean_object* v_toMonadRef_120_; lean_object* v_getCurrMacroScope_121_; lean_object* v_getContext_122_; lean_object* v_toBind_123_; lean_object* v_toPure_124_; lean_object* v_val_125_; lean_object* v_getRef_126_; lean_object* v_withRef_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v_toMonadRef_120_ = lean_ctor_get(v_inst_117_, 0);
lean_inc_ref(v_toMonadRef_120_);
v_getCurrMacroScope_121_ = lean_ctor_get(v_inst_117_, 1);
lean_inc(v_getCurrMacroScope_121_);
v_getContext_122_ = lean_ctor_get(v_inst_117_, 2);
lean_inc(v_getContext_122_);
lean_dec_ref(v_inst_117_);
v_toBind_123_ = lean_ctor_get(v_inst_116_, 1);
lean_inc(v_toBind_123_);
lean_dec_ref(v_inst_116_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc(v_toPure_124_);
lean_dec_ref(v_toApplicative_119_);
v_val_125_ = lean_ctor_get(v_term_x3f_118_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v_term_x3f_118_);
v_getRef_126_ = lean_ctor_get(v_toMonadRef_120_, 0);
lean_inc(v_getRef_126_);
v_withRef_127_ = lean_ctor_get(v_toMonadRef_120_, 1);
lean_inc(v_withRef_127_);
lean_dec_ref(v_toMonadRef_120_);
lean_inc(v_toPure_124_);
v___f_128_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_128_, 0, v_toPure_124_);
lean_inc(v_toBind_123_);
lean_inc(v_val_125_);
v___f_129_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 6, 5);
lean_closure_set(v___f_129_, 0, v_val_125_);
lean_closure_set(v___f_129_, 1, v_toPure_124_);
lean_closure_set(v___f_129_, 2, v_toBind_123_);
lean_closure_set(v___f_129_, 3, v_getContext_122_);
lean_closure_set(v___f_129_, 4, v_getCurrMacroScope_121_);
lean_inc(v_toBind_123_);
lean_inc(v_getRef_126_);
v___x_130_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v_getRef_126_, v___f_128_);
lean_inc(v_toBind_123_);
v___x_131_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_130_, v___f_129_);
v___f_132_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_132_, 0, v_val_125_);
lean_closure_set(v___f_132_, 1, v_withRef_127_);
lean_closure_set(v___f_132_, 2, v___x_131_);
v___x_133_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v_getRef_126_, v___f_132_);
return v___x_133_;
}
else
{
lean_object* v_toMonadRef_134_; lean_object* v_getCurrMacroScope_135_; lean_object* v_getContext_136_; lean_object* v_toBind_137_; lean_object* v_toPure_138_; lean_object* v_getRef_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_term_x3f_118_);
v_toMonadRef_134_ = lean_ctor_get(v_inst_117_, 0);
lean_inc_ref(v_toMonadRef_134_);
v_getCurrMacroScope_135_ = lean_ctor_get(v_inst_117_, 1);
lean_inc(v_getCurrMacroScope_135_);
v_getContext_136_ = lean_ctor_get(v_inst_117_, 2);
lean_inc(v_getContext_136_);
lean_dec_ref(v_inst_117_);
v_toBind_137_ = lean_ctor_get(v_inst_116_, 1);
lean_inc(v_toBind_137_);
lean_dec_ref(v_inst_116_);
v_toPure_138_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc(v_toPure_138_);
lean_dec_ref(v_toApplicative_119_);
v_getRef_139_ = lean_ctor_get(v_toMonadRef_134_, 0);
lean_inc(v_getRef_139_);
lean_dec_ref(v_toMonadRef_134_);
lean_inc(v_toPure_138_);
v___f_140_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_140_, 0, v_toPure_138_);
lean_inc(v_toBind_137_);
v___f_141_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7), 5, 4);
lean_closure_set(v___f_141_, 0, v_toPure_138_);
lean_closure_set(v___f_141_, 1, v_toBind_137_);
lean_closure_set(v___f_141_, 2, v_getContext_136_);
lean_closure_set(v___f_141_, 3, v_getCurrMacroScope_135_);
lean_inc(v_toBind_137_);
v___x_142_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v_getRef_139_, v___f_140_);
v___x_143_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_142_, v___f_141_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm(lean_object* v_m_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_term_x3f_147_){
_start:
{
lean_object* v_toApplicative_148_; 
v_toApplicative_148_ = lean_ctor_get(v_inst_145_, 0);
lean_inc_ref(v_toApplicative_148_);
if (lean_obj_tag(v_term_x3f_147_) == 1)
{
lean_object* v_toMonadRef_149_; lean_object* v_getCurrMacroScope_150_; lean_object* v_getContext_151_; lean_object* v_toBind_152_; lean_object* v_toPure_153_; lean_object* v_val_154_; lean_object* v_getRef_155_; lean_object* v_withRef_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___f_161_; lean_object* v___x_162_; 
v_toMonadRef_149_ = lean_ctor_get(v_inst_146_, 0);
lean_inc_ref(v_toMonadRef_149_);
v_getCurrMacroScope_150_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_getCurrMacroScope_150_);
v_getContext_151_ = lean_ctor_get(v_inst_146_, 2);
lean_inc(v_getContext_151_);
lean_dec_ref(v_inst_146_);
v_toBind_152_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_152_);
lean_dec_ref(v_inst_145_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc(v_toPure_153_);
lean_dec_ref(v_toApplicative_148_);
v_val_154_ = lean_ctor_get(v_term_x3f_147_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_term_x3f_147_);
v_getRef_155_ = lean_ctor_get(v_toMonadRef_149_, 0);
lean_inc(v_getRef_155_);
v_withRef_156_ = lean_ctor_get(v_toMonadRef_149_, 1);
lean_inc(v_withRef_156_);
lean_dec_ref(v_toMonadRef_149_);
lean_inc(v_toPure_153_);
v___f_157_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_157_, 0, v_toPure_153_);
lean_inc(v_toBind_152_);
lean_inc(v_val_154_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 6, 5);
lean_closure_set(v___f_158_, 0, v_val_154_);
lean_closure_set(v___f_158_, 1, v_toPure_153_);
lean_closure_set(v___f_158_, 2, v_toBind_152_);
lean_closure_set(v___f_158_, 3, v_getContext_151_);
lean_closure_set(v___f_158_, 4, v_getCurrMacroScope_150_);
lean_inc(v_toBind_152_);
lean_inc(v_getRef_155_);
v___x_159_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v_getRef_155_, v___f_157_);
lean_inc(v_toBind_152_);
v___x_160_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_159_, v___f_158_);
v___f_161_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_161_, 0, v_val_154_);
lean_closure_set(v___f_161_, 1, v_withRef_156_);
lean_closure_set(v___f_161_, 2, v___x_160_);
v___x_162_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v_getRef_155_, v___f_161_);
return v___x_162_;
}
else
{
lean_object* v_toMonadRef_163_; lean_object* v_getCurrMacroScope_164_; lean_object* v_getContext_165_; lean_object* v_toBind_166_; lean_object* v_toPure_167_; lean_object* v_getRef_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_term_x3f_147_);
v_toMonadRef_163_ = lean_ctor_get(v_inst_146_, 0);
lean_inc_ref(v_toMonadRef_163_);
v_getCurrMacroScope_164_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_getCurrMacroScope_164_);
v_getContext_165_ = lean_ctor_get(v_inst_146_, 2);
lean_inc(v_getContext_165_);
lean_dec_ref(v_inst_146_);
v_toBind_166_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_166_);
lean_dec_ref(v_inst_145_);
v_toPure_167_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc(v_toPure_167_);
lean_dec_ref(v_toApplicative_148_);
v_getRef_168_ = lean_ctor_get(v_toMonadRef_163_, 0);
lean_inc(v_getRef_168_);
lean_dec_ref(v_toMonadRef_163_);
lean_inc(v_toPure_167_);
v___f_169_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v_toPure_167_);
lean_inc(v_toBind_166_);
v___f_170_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7), 5, 4);
lean_closure_set(v___f_170_, 0, v_toPure_167_);
lean_closure_set(v___f_170_, 1, v_toBind_166_);
lean_closure_set(v___f_170_, 2, v_getContext_165_);
lean_closure_set(v___f_170_, 3, v_getCurrMacroScope_164_);
lean_inc(v_toBind_166_);
v___x_171_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v_getRef_168_, v___f_169_);
v___x_172_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v___x_171_, v___f_170_);
return v___x_172_;
}
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0));
v___x_175_ = l_String_toRawSubstring_x27(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(lean_object* v___x_182_, lean_object* v___x_183_, lean_object* v_tk_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_val_188_, lean_object* v___x_189_, lean_object* v_x_190_, lean_object* v_rev_x3f_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v_a_225_; lean_object* v_a_226_; lean_object* v_subDir_x3f_248_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_Lean_Syntax_getArg(v___x_185_, v___x_186_);
v___x_274_ = l_Lean_Syntax_isNone(v___x_273_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
lean_inc(v___x_273_);
v___x_275_ = l_Lean_Syntax_matchesNull(v___x_273_, v___x_187_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v___x_273_);
lean_dec(v_rev_x3f_191_);
lean_dec(v___x_183_);
lean_dec_ref(v___x_182_);
v___x_276_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
v___x_277_ = l_Lean_Macro_throwErrorAt___redArg(v_val_188_, v___x_276_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v___x_277_;
}
else
{
lean_object* v_subDir_x3f_278_; lean_object* v___x_279_; 
v_subDir_x3f_278_ = l_Lean_Syntax_getArg(v___x_273_, v___x_189_);
lean_dec(v___x_273_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_subDir_x3f_278_);
v_subDir_x3f_248_ = v___x_279_;
goto v___jp_247_;
}
}
else
{
lean_object* v___x_280_; 
lean_dec(v___x_273_);
v___x_280_ = lean_box(0);
v_subDir_x3f_248_ = v___x_280_;
goto v___jp_247_;
}
v___jp_194_:
{
uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_201_ = 0;
v___x_202_ = l_Lean_SourceInfo_fromRef(v___y_198_, v___x_201_);
lean_dec(v___y_198_);
v___x_203_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_204_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1);
v___x_205_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2));
v___x_206_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3));
v___x_207_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4));
v___x_208_ = l_Lean_addMacroScope(v___y_196_, v___x_207_, v___y_197_);
v___x_209_ = l_Lean_Name_mkStr3(v___x_182_, v___x_205_, v___x_206_);
v___x_210_ = lean_box(0);
lean_inc(v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_209_);
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_210_);
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_211_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
lean_inc(v___x_202_);
v___x_215_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_202_);
lean_ctor_set(v___x_215_, 1, v___x_204_);
lean_ctor_set(v___x_215_, 2, v___x_208_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
v___x_216_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_202_);
v___x_217_ = l_Lean_Syntax_node3(v___x_202_, v___x_216_, v___x_183_, v___y_195_, v_a_199_);
v___x_218_ = l_Lean_Syntax_node2(v___x_202_, v___x_203_, v___x_215_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_200_);
return v___x_219_;
}
v___jp_220_:
{
if (lean_obj_tag(v___y_222_) == 1)
{
lean_object* v_val_227_; lean_object* v_ref_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_val_227_ = lean_ctor_get(v___y_222_, 0);
lean_inc(v_val_227_);
lean_dec_ref(v___y_222_);
v_ref_228_ = l_Lean_replaceRef(v_val_227_, v___y_224_);
v___x_229_ = 0;
v___x_230_ = l_Lean_SourceInfo_fromRef(v_ref_228_, v___x_229_);
lean_dec(v_ref_228_);
v___x_231_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_232_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_233_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v___y_223_);
lean_inc(v___y_221_);
v___x_234_ = l_Lean_addMacroScope(v___y_221_, v___x_233_, v___y_223_);
v___x_235_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_230_);
v___x_236_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_236_, 0, v___x_230_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
lean_ctor_set(v___x_236_, 2, v___x_234_);
lean_ctor_set(v___x_236_, 3, v___x_235_);
v___x_237_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_230_);
v___x_238_ = l_Lean_Syntax_node1(v___x_230_, v___x_237_, v_val_227_);
v___x_239_ = l_Lean_Syntax_node2(v___x_230_, v___x_231_, v___x_236_, v___x_238_);
v___y_195_ = v_a_225_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v_a_199_ = v___x_239_;
v_a_200_ = v_a_226_;
goto v___jp_194_;
}
else
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___y_222_);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v___y_224_, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_243_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v___y_223_);
lean_inc(v___y_221_);
v___x_244_ = l_Lean_addMacroScope(v___y_221_, v___x_243_, v___y_223_);
v___x_245_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_246_, 0, v___x_241_);
lean_ctor_set(v___x_246_, 1, v___x_242_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v___x_245_);
v___y_195_ = v_a_225_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v_a_199_ = v___x_246_;
v_a_200_ = v_a_226_;
goto v___jp_194_;
}
}
v___jp_247_:
{
lean_object* v_quotContext_249_; lean_object* v_currMacroScope_250_; lean_object* v_ref_251_; lean_object* v_ref_252_; 
v_quotContext_249_ = lean_ctor_get(v___y_192_, 1);
lean_inc(v_quotContext_249_);
v_currMacroScope_250_ = lean_ctor_get(v___y_192_, 2);
lean_inc(v_currMacroScope_250_);
v_ref_251_ = lean_ctor_get(v___y_192_, 5);
lean_inc(v_ref_251_);
lean_dec_ref(v___y_192_);
v_ref_252_ = l_Lean_replaceRef(v_tk_184_, v_ref_251_);
lean_dec(v_ref_251_);
if (lean_obj_tag(v_rev_x3f_191_) == 1)
{
lean_object* v_val_253_; lean_object* v_ref_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_val_253_ = lean_ctor_get(v_rev_x3f_191_, 0);
lean_inc(v_val_253_);
lean_dec_ref(v_rev_x3f_191_);
v_ref_254_ = l_Lean_replaceRef(v_val_253_, v_ref_252_);
v___x_255_ = 0;
v___x_256_ = l_Lean_SourceInfo_fromRef(v_ref_254_, v___x_255_);
lean_dec(v_ref_254_);
v___x_257_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_258_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_259_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_250_);
lean_inc(v_quotContext_249_);
v___x_260_ = l_Lean_addMacroScope(v_quotContext_249_, v___x_259_, v_currMacroScope_250_);
v___x_261_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_256_);
v___x_262_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_262_, 0, v___x_256_);
lean_ctor_set(v___x_262_, 1, v___x_258_);
lean_ctor_set(v___x_262_, 2, v___x_260_);
lean_ctor_set(v___x_262_, 3, v___x_261_);
v___x_263_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_256_);
v___x_264_ = l_Lean_Syntax_node1(v___x_256_, v___x_263_, v_val_253_);
v___x_265_ = l_Lean_Syntax_node2(v___x_256_, v___x_257_, v___x_262_, v___x_264_);
v___y_221_ = v_quotContext_249_;
v___y_222_ = v_subDir_x3f_248_;
v___y_223_ = v_currMacroScope_250_;
v___y_224_ = v_ref_252_;
v_a_225_ = v___x_265_;
v_a_226_ = v___y_193_;
goto v___jp_220_;
}
else
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_rev_x3f_191_);
v___x_266_ = 0;
v___x_267_ = l_Lean_SourceInfo_fromRef(v_ref_252_, v___x_266_);
v___x_268_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_269_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v_currMacroScope_250_);
lean_inc(v_quotContext_249_);
v___x_270_ = l_Lean_addMacroScope(v_quotContext_249_, v___x_269_, v_currMacroScope_250_);
v___x_271_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v___x_267_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_270_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
v___y_221_ = v_quotContext_249_;
v___y_222_ = v_subDir_x3f_248_;
v___y_223_ = v_currMacroScope_250_;
v___y_224_ = v_ref_252_;
v_a_225_ = v___x_272_;
v_a_226_ = v___y_193_;
goto v___jp_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___boxed(lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v_tk_283_, lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v___x_286_, lean_object* v_val_287_, lean_object* v___x_288_, lean_object* v_x_289_, lean_object* v_rev_x3f_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_281_, v___x_282_, v_tk_283_, v___x_284_, v___x_285_, v___x_286_, v_val_287_, v___x_288_, v_x_289_, v_rev_x3f_290_, v___y_291_, v___y_292_);
lean_dec(v___x_288_);
lean_dec(v_val_287_);
lean_dec(v___x_286_);
lean_dec(v___x_285_);
lean_dec(v___x_284_);
lean_dec(v_tk_283_);
return v_res_293_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3));
v___x_299_ = l_String_toRawSubstring_x27(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_304_ = l_String_toRawSubstring_x27(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9));
v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12));
v___x_314_ = l_String_toRawSubstring_x27(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26));
v___x_333_ = l_String_toRawSubstring_x27(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38));
v___x_350_ = l_Lean_mkCIdent(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44));
v___x_357_ = l_String_toRawSubstring_x27(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Array_mkArray0(lean_box(0));
return v___x_378_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80));
v___x_430_ = l_String_toRawSubstring_x27(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110));
v___x_495_ = l_String_toRawSubstring_x27(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(lean_object* v_stx_530_, lean_object* v_doc_x3f_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15));
v___x_658_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18));
lean_inc(v_stx_530_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_doc_x3f_531_);
v___x_660_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_661_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_660_, v_a_532_, v_a_533_);
lean_dec(v_stx_530_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_772_; lean_object* v_quotContext_773_; lean_object* v_currMacroScope_774_; lean_object* v_ref_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v_a_780_; lean_object* v_a_781_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v_ver_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v_a_968_; lean_object* v_a_969_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v_opts_x3f_987_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v_src_x3f_1041_; lean_object* v_ver_x3f_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_1074_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_664_);
v___x_1075_ = l_Lean_Syntax_isNone(v___x_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; 
lean_inc(v___x_1074_);
v___x_1076_ = l_Lean_Syntax_matchesNull(v___x_1074_, v___x_664_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v___x_1074_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1077_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1078_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1077_, v_a_532_, v_a_533_);
lean_dec(v_stx_530_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = l_Lean_Syntax_getArg(v___x_1074_, v___x_662_);
lean_dec(v___x_1074_);
v___x_1080_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124));
lean_inc(v___x_1079_);
v___x_1081_ = l_Lean_Syntax_isOfKind(v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v___x_1079_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1082_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1083_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1082_, v_a_532_, v_a_533_);
lean_dec(v_stx_530_);
return v___x_1083_;
}
else
{
lean_object* v_ver_x3f_1084_; lean_object* v___x_1085_; 
v_ver_x3f_1084_ = l_Lean_Syntax_getArg(v___x_1079_, v___x_664_);
lean_dec(v___x_1079_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_ver_x3f_1084_);
v_ver_x3f_1057_ = v___x_1085_;
v___y_1058_ = v_a_532_;
v___y_1059_ = v_a_533_;
goto v___jp_1056_;
}
}
}
else
{
lean_object* v___x_1086_; 
lean_dec(v___x_1074_);
v___x_1086_ = lean_box(0);
v_ver_x3f_1057_ = v___x_1086_;
v___y_1058_ = v_a_532_;
v___y_1059_ = v_a_533_;
goto v___jp_1056_;
}
v___jp_665_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_692_ = l_Array_append___redArg(v___y_690_, v___y_691_);
lean_dec_ref(v___y_691_);
lean_inc(v___y_675_);
lean_inc(v___y_684_);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___y_684_);
lean_ctor_set(v___x_693_, 1, v___y_675_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
v___x_694_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_695_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_694_);
v___x_696_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21));
lean_inc(v___y_684_);
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___y_684_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_699_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_701_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_700_);
lean_inc(v___y_686_);
lean_inc(v___y_684_);
v___x_702_ = l_Lean_Syntax_node1(v___y_684_, v___x_701_, v___y_686_);
v___x_703_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24));
v___x_704_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_705_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___x_703_, v___x_704_);
v___x_706_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27);
v___x_707_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28));
lean_inc(v___y_671_);
lean_inc(v___y_667_);
v___x_708_ = l_Lean_addMacroScope(v___y_667_, v___x_707_, v___y_671_);
v___x_709_ = lean_box(0);
lean_inc(v___y_684_);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___y_684_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
lean_inc(v___y_686_);
lean_inc(v___y_684_);
v___x_711_ = l_Lean_Syntax_node2(v___y_684_, v___x_705_, v___x_710_, v___y_686_);
lean_inc(v___y_684_);
v___x_712_ = l_Lean_Syntax_node2(v___y_684_, v___x_699_, v___x_702_, v___x_711_);
lean_inc(v___y_675_);
lean_inc(v___y_684_);
v___x_713_ = l_Lean_Syntax_node1(v___y_684_, v___y_675_, v___x_712_);
v___x_714_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29));
lean_inc(v___y_684_);
v___x_715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_715_, 0, v___y_684_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
lean_inc(v___y_684_);
v___x_716_ = l_Lean_Syntax_node3(v___y_684_, v___x_695_, v___x_697_, v___x_713_, v___x_715_);
lean_inc(v___y_675_);
lean_inc(v___y_684_);
v___x_717_ = l_Lean_Syntax_node1(v___y_684_, v___y_675_, v___x_716_);
lean_inc_n(v___y_686_, 5);
lean_inc(v___y_684_);
v___x_718_ = l_Lean_Syntax_node7(v___y_684_, v___y_685_, v___x_693_, v___x_717_, v___y_686_, v___y_686_, v___y_686_, v___y_686_, v___y_686_);
v___x_719_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30));
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_720_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_688_, v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31));
lean_inc(v___y_684_);
v___x_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_722_, 0, v___y_684_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32));
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_724_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_688_, v___x_723_);
v___x_725_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33));
v___x_726_ = lean_box(2);
lean_inc(v___y_675_);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___y_675_);
lean_ctor_set(v___x_727_, 2, v___x_725_);
v___x_728_ = lean_mk_empty_array_with_capacity(v___y_674_);
lean_inc(v___y_682_);
v___x_729_ = lean_array_push(v___x_728_, v___y_682_);
v___x_730_ = lean_array_push(v___x_729_, v___x_727_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v___x_726_);
lean_ctor_set(v___x_731_, 1, v___x_724_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34));
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_733_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_688_, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_735_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36));
lean_inc(v___y_684_);
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_684_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39);
lean_inc(v___y_684_);
v___x_739_ = l_Lean_Syntax_node2(v___y_684_, v___x_735_, v___x_737_, v___x_738_);
lean_inc(v___y_675_);
lean_inc(v___y_684_);
v___x_740_ = l_Lean_Syntax_node1(v___y_684_, v___y_675_, v___x_739_);
lean_inc(v___y_686_);
lean_inc(v___y_684_);
v___x_741_ = l_Lean_Syntax_node2(v___y_684_, v___x_733_, v___y_686_, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_743_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_688_, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41));
lean_inc(v___y_684_);
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___y_684_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_747_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_749_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_748_);
v___x_750_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45);
v___x_751_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46));
lean_inc(v___y_671_);
lean_inc(v___y_667_);
v___x_752_ = l_Lean_addMacroScope(v___y_667_, v___x_751_, v___y_671_);
lean_inc(v___y_684_);
v___x_753_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_753_, 0, v___y_684_);
lean_ctor_set(v___x_753_, 1, v___x_750_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
lean_ctor_set(v___x_753_, 3, v___x_709_);
lean_inc(v___y_686_);
lean_inc(v___x_749_);
lean_inc(v___y_684_);
v___x_754_ = l_Lean_Syntax_node2(v___y_684_, v___x_749_, v___x_753_, v___y_686_);
v___x_755_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_756_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_755_);
v___x_757_ = l_Lean_TSyntax_getId(v___y_682_);
lean_dec(v___y_682_);
lean_inc(v___x_757_);
v___x_758_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_709_, v___x_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v___y_683_);
v___x_759_ = l_Lean_quoteNameMk(v___x_757_);
v___y_590_ = v___y_666_;
v___y_591_ = v___x_745_;
v___y_592_ = v___y_667_;
v___y_593_ = v___y_668_;
v___y_594_ = v___y_669_;
v___y_595_ = v___x_741_;
v___y_596_ = v___y_670_;
v___y_597_ = v___y_671_;
v___y_598_ = v___y_672_;
v___y_599_ = v___x_754_;
v___y_600_ = v___y_673_;
v___y_601_ = v___y_676_;
v___y_602_ = v___y_675_;
v___y_603_ = v___y_677_;
v___y_604_ = v___y_678_;
v___y_605_ = v___y_679_;
v___y_606_ = v___x_749_;
v___y_607_ = v___y_680_;
v___y_608_ = v___y_681_;
v___y_609_ = v___x_709_;
v___y_610_ = v___x_747_;
v___y_611_ = v___x_720_;
v___y_612_ = v___y_684_;
v___y_613_ = v___x_718_;
v___y_614_ = v___x_731_;
v___y_615_ = v___y_687_;
v___y_616_ = v___y_686_;
v___y_617_ = v___x_756_;
v___y_618_ = v___x_743_;
v___y_619_ = v___y_689_;
v___y_620_ = v___x_722_;
v___y_621_ = v___x_759_;
goto v___jp_589_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v___x_757_);
v_val_760_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_760_);
lean_dec_ref(v___x_758_);
v___x_761_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_679_);
v___x_762_ = l_Lean_Name_mkStr4(v___y_679_, v___y_670_, v___y_683_, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49));
v___x_764_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50));
v___x_765_ = lean_string_intercalate(v___x_764_, v_val_760_);
v___x_766_ = lean_string_append(v___x_763_, v___x_765_);
lean_dec_ref(v___x_765_);
v___x_767_ = l_Lean_Syntax_mkNameLit(v___x_766_, v___x_726_);
v___x_768_ = lean_mk_empty_array_with_capacity(v___x_664_);
v___x_769_ = lean_array_push(v___x_768_, v___x_767_);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_726_);
lean_ctor_set(v___x_770_, 1, v___x_762_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
v___y_590_ = v___y_666_;
v___y_591_ = v___x_745_;
v___y_592_ = v___y_667_;
v___y_593_ = v___y_668_;
v___y_594_ = v___y_669_;
v___y_595_ = v___x_741_;
v___y_596_ = v___y_670_;
v___y_597_ = v___y_671_;
v___y_598_ = v___y_672_;
v___y_599_ = v___x_754_;
v___y_600_ = v___y_673_;
v___y_601_ = v___y_676_;
v___y_602_ = v___y_675_;
v___y_603_ = v___y_677_;
v___y_604_ = v___y_678_;
v___y_605_ = v___y_679_;
v___y_606_ = v___x_749_;
v___y_607_ = v___y_680_;
v___y_608_ = v___y_681_;
v___y_609_ = v___x_709_;
v___y_610_ = v___x_747_;
v___y_611_ = v___x_720_;
v___y_612_ = v___y_684_;
v___y_613_ = v___x_718_;
v___y_614_ = v___x_731_;
v___y_615_ = v___y_687_;
v___y_616_ = v___y_686_;
v___y_617_ = v___x_756_;
v___y_618_ = v___x_743_;
v___y_619_ = v___y_689_;
v___y_620_ = v___x_722_;
v___y_621_ = v___x_770_;
goto v___jp_589_;
}
}
v___jp_771_:
{
uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_782_ = 0;
v___x_783_ = l_Lean_SourceInfo_fromRef(v_ref_775_, v___x_782_);
lean_dec(v_ref_775_);
v___x_784_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52));
v___x_785_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54));
v___x_786_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55));
lean_inc(v___x_783_);
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_783_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56));
lean_inc(v___x_783_);
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_783_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
lean_inc_ref(v___x_789_);
lean_inc_ref(v___x_787_);
lean_inc(v___x_783_);
v___x_790_ = l_Lean_Syntax_node2(v___x_783_, v___x_785_, v___x_787_, v___x_789_);
v___x_791_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0));
v___x_792_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1));
v___x_793_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2));
v___x_794_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58));
v___x_795_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_796_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59);
lean_inc(v___x_783_);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_783_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
lean_ctor_set(v___x_797_, 2, v___x_796_);
v___x_798_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61));
lean_inc_ref(v___x_797_);
lean_inc(v___x_783_);
v___x_799_ = l_Lean_Syntax_node1(v___x_783_, v___x_798_, v___x_797_);
v___x_800_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63));
lean_inc_ref(v___x_797_);
lean_inc(v___x_783_);
v___x_801_ = l_Lean_Syntax_node1(v___x_783_, v___x_800_, v___x_797_);
lean_inc_ref(v___x_789_);
lean_inc(v___x_801_);
lean_inc_ref_n(v___x_797_, 2);
lean_inc_ref(v___x_787_);
lean_inc(v___x_783_);
v___x_802_ = l_Lean_Syntax_node6(v___x_783_, v___x_794_, v___x_787_, v___x_797_, v___x_799_, v___x_801_, v___x_797_, v___x_789_);
lean_inc(v___x_783_);
v___x_803_ = l_Lean_Syntax_node2(v___x_783_, v___x_784_, v___x_790_, v___x_802_);
v___x_804_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64));
v___x_805_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66));
v___x_806_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68));
if (lean_obj_tag(v_doc_x3f_531_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_808_; 
v_val_807_ = lean_ctor_get(v_doc_x3f_531_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v_doc_x3f_531_);
v___x_808_ = l_Array_mkArray1___redArg(v_val_807_);
v___y_666_ = v_a_781_;
v___y_667_ = v_quotContext_773_;
v___y_668_ = v___x_805_;
v___y_669_ = v_a_780_;
v___y_670_ = v___x_792_;
v___y_671_ = v_currMacroScope_774_;
v___y_672_ = v___x_801_;
v___y_673_ = v___x_803_;
v___y_674_ = v___y_777_;
v___y_675_ = v___x_795_;
v___y_676_ = v___y_776_;
v___y_677_ = v___y_778_;
v___y_678_ = v___x_787_;
v___y_679_ = v___x_791_;
v___y_680_ = v___x_789_;
v___y_681_ = v___x_798_;
v___y_682_ = v___y_772_;
v___y_683_ = v___x_793_;
v___y_684_ = v___x_783_;
v___y_685_ = v___x_806_;
v___y_686_ = v___x_797_;
v___y_687_ = v___x_794_;
v___y_688_ = v___x_804_;
v___y_689_ = v___y_779_;
v___y_690_ = v___x_796_;
v___y_691_ = v___x_808_;
goto v___jp_665_;
}
else
{
lean_object* v___x_809_; 
lean_dec(v_doc_x3f_531_);
v___x_809_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69));
v___y_666_ = v_a_781_;
v___y_667_ = v_quotContext_773_;
v___y_668_ = v___x_805_;
v___y_669_ = v_a_780_;
v___y_670_ = v___x_792_;
v___y_671_ = v_currMacroScope_774_;
v___y_672_ = v___x_801_;
v___y_673_ = v___x_803_;
v___y_674_ = v___y_777_;
v___y_675_ = v___x_795_;
v___y_676_ = v___y_776_;
v___y_677_ = v___y_778_;
v___y_678_ = v___x_787_;
v___y_679_ = v___x_791_;
v___y_680_ = v___x_789_;
v___y_681_ = v___x_798_;
v___y_682_ = v___y_772_;
v___y_683_ = v___x_793_;
v___y_684_ = v___x_783_;
v___y_685_ = v___x_806_;
v___y_686_ = v___x_797_;
v___y_687_ = v___x_794_;
v___y_688_ = v___x_804_;
v___y_689_ = v___y_779_;
v___y_690_ = v___x_796_;
v___y_691_ = v___x_809_;
goto v___jp_665_;
}
}
v___jp_810_:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_814_);
if (lean_obj_tag(v___y_811_) == 1)
{
lean_object* v_val_820_; lean_object* v_quotContext_821_; lean_object* v_currMacroScope_822_; lean_object* v_ref_823_; lean_object* v_ref_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_val_820_ = lean_ctor_get(v___y_811_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v___y_811_);
v_quotContext_821_ = lean_ctor_get(v___y_817_, 1);
lean_inc(v_quotContext_821_);
v_currMacroScope_822_ = lean_ctor_get(v___y_817_, 2);
lean_inc(v_currMacroScope_822_);
v_ref_823_ = lean_ctor_get(v___y_817_, 5);
lean_inc(v_ref_823_);
lean_dec_ref(v___y_817_);
v_ref_824_ = l_Lean_replaceRef(v_val_820_, v_ref_823_);
v___x_825_ = 0;
v___x_826_ = l_Lean_SourceInfo_fromRef(v_ref_824_, v___x_825_);
lean_dec(v_ref_824_);
v___x_827_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_828_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_829_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_822_);
lean_inc(v_quotContext_821_);
v___x_830_ = l_Lean_addMacroScope(v_quotContext_821_, v___x_829_, v_currMacroScope_822_);
v___x_831_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_826_);
v___x_832_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_832_, 0, v___x_826_);
lean_ctor_set(v___x_832_, 1, v___x_828_);
lean_ctor_set(v___x_832_, 2, v___x_830_);
lean_ctor_set(v___x_832_, 3, v___x_831_);
v___x_833_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_826_);
v___x_834_ = l_Lean_Syntax_node1(v___x_826_, v___x_833_, v_val_820_);
v___x_835_ = l_Lean_Syntax_node2(v___x_826_, v___x_827_, v___x_832_, v___x_834_);
v___y_772_ = v___x_819_;
v_quotContext_773_ = v_quotContext_821_;
v_currMacroScope_774_ = v_currMacroScope_822_;
v_ref_775_ = v_ref_823_;
v___y_776_ = v___y_813_;
v___y_777_ = v___y_812_;
v___y_778_ = v_ver_816_;
v___y_779_ = v___y_815_;
v_a_780_ = v___x_835_;
v_a_781_ = v___y_818_;
goto v___jp_771_;
}
else
{
lean_object* v_quotContext_836_; lean_object* v_currMacroScope_837_; lean_object* v_ref_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___y_811_);
v_quotContext_836_ = lean_ctor_get(v___y_817_, 1);
lean_inc(v_quotContext_836_);
v_currMacroScope_837_ = lean_ctor_get(v___y_817_, 2);
lean_inc(v_currMacroScope_837_);
v_ref_838_ = lean_ctor_get(v___y_817_, 5);
lean_inc(v_ref_838_);
lean_dec_ref(v___y_817_);
v___x_839_ = 0;
v___x_840_ = l_Lean_SourceInfo_fromRef(v_ref_838_, v___x_839_);
v___x_841_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_842_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v_currMacroScope_837_);
lean_inc(v_quotContext_836_);
v___x_843_ = l_Lean_addMacroScope(v_quotContext_836_, v___x_842_, v_currMacroScope_837_);
v___x_844_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_845_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_845_, 0, v___x_840_);
lean_ctor_set(v___x_845_, 1, v___x_841_);
lean_ctor_set(v___x_845_, 2, v___x_843_);
lean_ctor_set(v___x_845_, 3, v___x_844_);
v___y_772_ = v___x_819_;
v_quotContext_773_ = v_quotContext_836_;
v_currMacroScope_774_ = v_currMacroScope_837_;
v_ref_775_ = v_ref_838_;
v___y_776_ = v___y_813_;
v___y_777_ = v___y_812_;
v___y_778_ = v_ver_816_;
v___y_779_ = v___y_815_;
v_a_780_ = v___x_845_;
v_a_781_ = v___y_818_;
goto v___jp_771_;
}
}
v___jp_846_:
{
if (lean_obj_tag(v___y_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_a_855_; 
v_a_854_ = lean_ctor_get(v___y_853_, 0);
lean_inc(v_a_854_);
v_a_855_ = lean_ctor_get(v___y_853_, 1);
lean_inc(v_a_855_);
lean_dec_ref(v___y_853_);
v___y_811_ = v___y_847_;
v___y_812_ = v___y_849_;
v___y_813_ = v___y_848_;
v___y_814_ = v___y_850_;
v___y_815_ = v___y_851_;
v_ver_816_ = v_a_854_;
v___y_817_ = v___y_852_;
v___y_818_ = v_a_855_;
goto v___jp_810_;
}
else
{
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec(v___y_850_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v_doc_x3f_531_);
return v___y_853_;
}
}
v___jp_856_:
{
if (lean_obj_tag(v___y_861_) == 1)
{
lean_object* v_val_865_; lean_object* v_methods_866_; lean_object* v_quotContext_867_; lean_object* v_currMacroScope_868_; lean_object* v_currRecDepth_869_; lean_object* v_maxRecDepth_870_; lean_object* v_ref_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v_ref_874_; lean_object* v___x_875_; 
v_val_865_ = lean_ctor_get(v___y_861_, 0);
lean_inc(v_val_865_);
lean_dec_ref(v___y_861_);
v_methods_866_ = lean_ctor_get(v___y_863_, 0);
v_quotContext_867_ = lean_ctor_get(v___y_863_, 1);
v_currMacroScope_868_ = lean_ctor_get(v___y_863_, 2);
v_currRecDepth_869_ = lean_ctor_get(v___y_863_, 3);
v_maxRecDepth_870_ = lean_ctor_get(v___y_863_, 4);
v_ref_871_ = lean_ctor_get(v___y_863_, 5);
v___x_872_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71));
lean_inc(v_val_865_);
v___x_873_ = l_Lean_Syntax_isOfKind(v_val_865_, v___x_872_);
v_ref_874_ = l_Lean_replaceRef(v_val_865_, v_ref_871_);
lean_inc(v_ref_874_);
lean_inc(v_maxRecDepth_870_);
lean_inc(v_currRecDepth_869_);
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
lean_inc(v_methods_866_);
v___x_875_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_875_, 0, v_methods_866_);
lean_ctor_set(v___x_875_, 1, v_quotContext_867_);
lean_ctor_set(v___x_875_, 2, v_currMacroScope_868_);
lean_ctor_set(v___x_875_, 3, v_currRecDepth_869_);
lean_ctor_set(v___x_875_, 4, v_maxRecDepth_870_);
lean_ctor_set(v___x_875_, 5, v_ref_874_);
if (v___x_873_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec(v_ref_874_);
v___x_876_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72));
v___x_877_ = l_Lean_Macro_throwErrorAt___redArg(v_val_865_, v___x_876_, v___x_875_, v___y_857_);
lean_dec_ref(v___x_875_);
lean_dec(v_val_865_);
v___y_847_ = v___y_858_;
v___y_848_ = v___y_864_;
v___y_849_ = v___y_859_;
v___y_850_ = v___y_860_;
v___y_851_ = v___y_862_;
v___y_852_ = v___y_863_;
v___y_853_ = v___x_877_;
goto v___jp_846_;
}
else
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = l_Lean_Syntax_getArg(v_val_865_, v___x_662_);
lean_inc(v___x_878_);
v___x_879_ = l_Lean_Syntax_matchesNull(v___x_878_, v___x_664_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; 
v___x_880_ = l_Lean_Syntax_matchesNull(v___x_878_, v___x_662_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_ref_874_);
v___x_881_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72));
v___x_882_ = l_Lean_Macro_throwErrorAt___redArg(v_val_865_, v___x_881_, v___x_875_, v___y_857_);
lean_dec_ref(v___x_875_);
lean_dec(v_val_865_);
v___y_847_ = v___y_858_;
v___y_848_ = v___y_864_;
v___y_849_ = v___y_859_;
v___y_850_ = v___y_860_;
v___y_851_ = v___y_862_;
v___y_852_ = v___y_863_;
v___y_853_ = v___x_882_;
goto v___jp_846_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v___x_875_);
v___x_883_ = l_Lean_Syntax_getArg(v_val_865_, v___x_664_);
lean_dec(v_val_865_);
v___x_884_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___x_879_);
lean_dec(v_ref_874_);
v___x_885_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_886_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_887_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
v___x_888_ = l_Lean_addMacroScope(v_quotContext_867_, v___x_887_, v_currMacroScope_868_);
v___x_889_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_884_);
v___x_890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_890_, 0, v___x_884_);
lean_ctor_set(v___x_890_, 1, v___x_886_);
lean_ctor_set(v___x_890_, 2, v___x_888_);
lean_ctor_set(v___x_890_, 3, v___x_889_);
v___x_891_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_884_);
v___x_892_ = l_Lean_Syntax_node1(v___x_884_, v___x_891_, v___x_883_);
v___x_893_ = l_Lean_Syntax_node2(v___x_884_, v___x_885_, v___x_890_, v___x_892_);
v___y_811_ = v___y_858_;
v___y_812_ = v___y_859_;
v___y_813_ = v___y_864_;
v___y_814_ = v___y_860_;
v___y_815_ = v___y_862_;
v_ver_816_ = v___x_893_;
v___y_817_ = v___y_863_;
v___y_818_ = v___y_857_;
goto v___jp_810_;
}
}
else
{
lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v___x_878_);
lean_dec_ref(v___x_875_);
v___x_894_ = l_Lean_Syntax_getArg(v_val_865_, v___x_664_);
lean_dec(v_val_865_);
v___x_895_ = 0;
v___x_896_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___x_895_);
lean_dec(v_ref_874_);
v___x_897_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_898_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_899_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
v___x_900_ = l_Lean_addMacroScope(v_quotContext_867_, v___x_899_, v_currMacroScope_868_);
v___x_901_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_896_);
v___x_902_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_898_);
lean_ctor_set(v___x_902_, 2, v___x_900_);
lean_ctor_set(v___x_902_, 3, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_904_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74));
v___x_905_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76));
v___x_906_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77));
lean_inc(v___x_896_);
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_896_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79));
v___x_909_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81);
v___x_910_ = lean_box(0);
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
v___x_911_ = l_Lean_addMacroScope(v_quotContext_867_, v___x_910_, v_currMacroScope_868_);
v___x_912_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93));
lean_inc(v___x_896_);
v___x_913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_913_, 0, v___x_896_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
lean_ctor_set(v___x_913_, 2, v___x_911_);
lean_ctor_set(v___x_913_, 3, v___x_912_);
lean_inc(v___x_896_);
v___x_914_ = l_Lean_Syntax_node1(v___x_896_, v___x_908_, v___x_913_);
lean_inc(v___x_896_);
v___x_915_ = l_Lean_Syntax_node2(v___x_896_, v___x_905_, v___x_907_, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95));
v___x_917_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97));
v___x_918_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98));
lean_inc(v___x_896_);
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_896_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
lean_inc(v___x_896_);
v___x_920_ = l_Lean_Syntax_node1(v___x_896_, v___x_917_, v___x_919_);
v___x_921_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99));
lean_inc(v___x_896_);
v___x_922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_896_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
lean_inc(v___x_896_);
v___x_923_ = l_Lean_Syntax_node3(v___x_896_, v___x_916_, v___x_920_, v___x_922_, v___x_894_);
v___x_924_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100));
lean_inc(v___x_896_);
v___x_925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_896_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_inc(v___x_896_);
v___x_926_ = l_Lean_Syntax_node3(v___x_896_, v___x_904_, v___x_915_, v___x_923_, v___x_925_);
lean_inc(v___x_896_);
v___x_927_ = l_Lean_Syntax_node1(v___x_896_, v___x_903_, v___x_926_);
v___x_928_ = l_Lean_Syntax_node2(v___x_896_, v___x_897_, v___x_902_, v___x_927_);
v___y_811_ = v___y_858_;
v___y_812_ = v___y_859_;
v___y_813_ = v___y_864_;
v___y_814_ = v___y_860_;
v___y_815_ = v___y_862_;
v_ver_816_ = v___x_928_;
v___y_817_ = v___y_863_;
v___y_818_ = v___y_857_;
goto v___jp_810_;
}
}
}
else
{
lean_object* v_quotContext_929_; lean_object* v_currMacroScope_930_; lean_object* v_ref_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___y_861_);
v_quotContext_929_ = lean_ctor_get(v___y_863_, 1);
v_currMacroScope_930_ = lean_ctor_get(v___y_863_, 2);
v_ref_931_ = lean_ctor_get(v___y_863_, 5);
v___x_932_ = 0;
v___x_933_ = l_Lean_SourceInfo_fromRef(v_ref_931_, v___x_932_);
v___x_934_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_935_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v_currMacroScope_930_);
lean_inc(v_quotContext_929_);
v___x_936_ = l_Lean_addMacroScope(v_quotContext_929_, v___x_935_, v_currMacroScope_930_);
v___x_937_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_938_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_938_, 0, v___x_933_);
lean_ctor_set(v___x_938_, 1, v___x_934_);
lean_ctor_set(v___x_938_, 2, v___x_936_);
lean_ctor_set(v___x_938_, 3, v___x_937_);
v___y_811_ = v___y_858_;
v___y_812_ = v___y_859_;
v___y_813_ = v___y_864_;
v___y_814_ = v___y_860_;
v___y_815_ = v___y_862_;
v_ver_816_ = v___x_938_;
v___y_817_ = v___y_863_;
v___y_818_ = v___y_857_;
goto v___jp_810_;
}
}
v___jp_939_:
{
uint8_t v___x_947_; 
lean_inc(v___x_663_);
v___x_947_ = l_Lean_Syntax_isOfKind(v___x_663_, v___y_941_);
lean_dec(v___y_941_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_a_945_);
lean_dec(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v_doc_x3f_531_);
v___x_948_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101));
v___x_949_ = l_Lean_Macro_throwErrorAt___redArg(v___x_663_, v___x_948_, v___y_944_, v_a_946_);
lean_dec_ref(v___y_944_);
lean_dec(v___x_663_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = l_Lean_Syntax_getArg(v___x_663_, v___x_662_);
v___x_951_ = l_Lean_Syntax_isNone(v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; 
lean_inc(v___x_950_);
v___x_952_ = l_Lean_Syntax_matchesNull(v___x_950_, v___y_940_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v___x_950_);
lean_dec(v_a_945_);
lean_dec(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v_doc_x3f_531_);
v___x_953_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101));
v___x_954_ = l_Lean_Macro_throwErrorAt___redArg(v___x_663_, v___x_953_, v___y_944_, v_a_946_);
lean_dec_ref(v___y_944_);
lean_dec(v___x_663_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Lean_Syntax_getArg(v___x_950_, v___x_662_);
lean_dec(v___x_950_);
v___x_956_ = l_Lean_Syntax_getArg(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
v___y_857_ = v_a_946_;
v___y_858_ = v_a_945_;
v___y_859_ = v___y_940_;
v___y_860_ = v___x_956_;
v___y_861_ = v___y_942_;
v___y_862_ = v___y_943_;
v___y_863_ = v___y_944_;
v___y_864_ = v___x_955_;
goto v___jp_856_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v___x_950_);
v___x_957_ = l_Lean_Syntax_getArg(v___x_663_, v___x_664_);
v___x_958_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80));
v___x_959_ = 0;
v___x_960_ = l_Lean_SourceInfo_fromRef(v___x_663_, v___x_959_);
lean_dec(v___x_663_);
v___x_961_ = l_Lean_Syntax_mkStrLit(v___x_958_, v___x_960_);
v___y_857_ = v_a_946_;
v___y_858_ = v_a_945_;
v___y_859_ = v___y_940_;
v___y_860_ = v___x_957_;
v___y_861_ = v___y_942_;
v___y_862_ = v___y_943_;
v___y_863_ = v___y_944_;
v___y_864_ = v___x_961_;
goto v___jp_856_;
}
}
}
v___jp_962_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_a_968_);
v___y_940_ = v___y_963_;
v___y_941_ = v___y_964_;
v___y_942_ = v___y_965_;
v___y_943_ = v___y_966_;
v___y_944_ = v___y_967_;
v_a_945_ = v___x_970_;
v_a_946_ = v_a_969_;
goto v___jp_939_;
}
v___jp_971_:
{
if (lean_obj_tag(v___y_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_a_979_; 
v_a_978_ = lean_ctor_get(v___y_977_, 0);
lean_inc(v_a_978_);
v_a_979_ = lean_ctor_get(v___y_977_, 1);
lean_inc(v_a_979_);
lean_dec_ref(v___y_977_);
v___y_963_ = v___y_972_;
v___y_964_ = v___y_973_;
v___y_965_ = v___y_974_;
v___y_966_ = v___y_975_;
v___y_967_ = v___y_976_;
v_a_968_ = v_a_978_;
v_a_969_ = v_a_979_;
goto v___jp_962_;
}
else
{
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
return v___y_977_;
}
}
v___jp_980_:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103));
if (lean_obj_tag(v___y_986_) == 0)
{
v___y_940_ = v___y_983_;
v___y_941_ = v___x_988_;
v___y_942_ = v___y_985_;
v___y_943_ = v_opts_x3f_987_;
v___y_944_ = v___y_982_;
v_a_945_ = v___y_986_;
v_a_946_ = v___y_984_;
goto v___jp_939_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1035_; 
v_val_989_ = lean_ctor_get(v___y_986_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___y_986_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_991_ = v___y_986_;
v_isShared_992_ = v_isSharedCheck_1035_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_val_989_);
lean_dec(v___y_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1035_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105));
lean_inc(v_val_989_);
v___x_994_ = l_Lean_Syntax_isOfKind(v_val_989_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_991_);
v___x_995_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
v___x_996_ = l_Lean_Macro_throwErrorAt___redArg(v_val_989_, v___x_995_, v___y_982_, v___y_984_);
lean_dec(v_val_989_);
v___y_972_ = v___y_983_;
v___y_973_ = v___x_988_;
v___y_974_ = v___y_985_;
v___y_975_ = v_opts_x3f_987_;
v___y_976_ = v___y_982_;
v___y_977_ = v___x_996_;
goto v___jp_971_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = l_Lean_Syntax_getArg(v_val_989_, v___x_662_);
v___x_998_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107));
lean_inc(v___x_997_);
v___x_999_ = l_Lean_Syntax_isOfKind(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
lean_del_object(v___x_991_);
v___x_1000_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109));
lean_inc(v___x_997_);
v___x_1001_ = l_Lean_Syntax_isOfKind(v___x_997_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v___x_997_);
v___x_1002_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
v___x_1003_ = l_Lean_Macro_throwErrorAt___redArg(v_val_989_, v___x_1002_, v___y_982_, v___y_984_);
lean_dec(v_val_989_);
v___y_972_ = v___y_983_;
v___y_973_ = v___x_988_;
v___y_974_ = v___y_985_;
v___y_975_ = v_opts_x3f_987_;
v___y_976_ = v___y_982_;
v___y_977_ = v___x_1003_;
goto v___jp_971_;
}
else
{
lean_object* v_quotContext_1004_; lean_object* v_currMacroScope_1005_; lean_object* v_ref_1006_; lean_object* v___x_1007_; lean_object* v_ref_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_quotContext_1004_ = lean_ctor_get(v___y_982_, 1);
v_currMacroScope_1005_ = lean_ctor_get(v___y_982_, 2);
v_ref_1006_ = lean_ctor_get(v___y_982_, 5);
v___x_1007_ = l_Lean_Syntax_getArg(v___x_997_, v___x_662_);
lean_dec(v___x_997_);
v_ref_1008_ = l_Lean_replaceRef(v_val_989_, v_ref_1006_);
lean_dec(v_val_989_);
v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1008_, v___x_999_);
lean_dec(v_ref_1008_);
v___x_1010_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_1011_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111);
v___x_1012_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113));
lean_inc(v_currMacroScope_1005_);
lean_inc(v_quotContext_1004_);
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1012_, v_currMacroScope_1005_);
v___x_1014_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc(v___x_1009_);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1009_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_1009_);
v___x_1017_ = l_Lean_Syntax_node1(v___x_1009_, v___x_1016_, v___x_1007_);
v___x_1018_ = l_Lean_Syntax_node2(v___x_1009_, v___x_1010_, v___x_1015_, v___x_1017_);
v___y_963_ = v___y_983_;
v___y_964_ = v___x_988_;
v___y_965_ = v___y_985_;
v___y_966_ = v_opts_x3f_987_;
v___y_967_ = v___y_982_;
v_a_968_ = v___x_1018_;
v_a_969_ = v___y_984_;
goto v___jp_962_;
}
}
else
{
lean_object* v_tk_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_tk_1019_ = l_Lean_Syntax_getArg(v___x_997_, v___x_662_);
v___x_1020_ = l_Lean_Syntax_getArg(v___x_997_, v___x_664_);
v___x_1021_ = l_Lean_Syntax_getArg(v___x_997_, v___y_983_);
v___x_1022_ = l_Lean_Syntax_isNone(v___x_1021_);
if (v___x_1022_ == 0)
{
uint8_t v___x_1023_; 
lean_inc(v___x_1021_);
v___x_1023_ = l_Lean_Syntax_matchesNull(v___x_1021_, v___y_983_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v___x_1021_);
lean_dec(v___x_1020_);
lean_dec(v_tk_1019_);
lean_dec(v___x_997_);
lean_del_object(v___x_991_);
v___x_1024_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
v___x_1025_ = l_Lean_Macro_throwErrorAt___redArg(v_val_989_, v___x_1024_, v___y_982_, v___y_984_);
lean_dec(v_val_989_);
v___y_972_ = v___y_983_;
v___y_973_ = v___x_988_;
v___y_974_ = v___y_985_;
v___y_975_ = v_opts_x3f_987_;
v___y_976_ = v___y_982_;
v___y_977_ = v___x_1025_;
goto v___jp_971_;
}
else
{
lean_object* v_rev_x3f_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v_rev_x3f_1026_ = l_Lean_Syntax_getArg(v___x_1021_, v___x_664_);
lean_dec(v___x_1021_);
v___x_1027_ = lean_box(0);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_rev_x3f_1026_);
v___x_1029_ = v___x_991_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_rev_x3f_1026_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
lean_inc_ref(v___y_982_);
v___x_1030_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_657_, v___x_1020_, v_tk_1019_, v___x_997_, v___y_981_, v___y_983_, v_val_989_, v___x_664_, v___x_1027_, v___x_1029_, v___y_982_, v___y_984_);
lean_dec(v_val_989_);
lean_dec(v___x_997_);
lean_dec(v_tk_1019_);
v___y_972_ = v___y_983_;
v___y_973_ = v___x_988_;
v___y_974_ = v___y_985_;
v___y_975_ = v_opts_x3f_987_;
v___y_976_ = v___y_982_;
v___y_977_ = v___x_1030_;
goto v___jp_971_;
}
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v___x_1021_);
lean_del_object(v___x_991_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_box(0);
lean_inc_ref(v___y_982_);
v___x_1034_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_657_, v___x_1020_, v_tk_1019_, v___x_997_, v___y_981_, v___y_983_, v_val_989_, v___x_664_, v___x_1032_, v___x_1033_, v___y_982_, v___y_984_);
lean_dec(v_val_989_);
lean_dec(v___x_997_);
lean_dec(v_tk_1019_);
v___y_972_ = v___y_983_;
v___y_973_ = v___x_988_;
v___y_974_ = v___y_985_;
v___y_975_ = v_opts_x3f_987_;
v___y_976_ = v___y_982_;
v___y_977_ = v___x_1034_;
goto v___jp_971_;
}
}
}
}
}
}
v___jp_1036_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(3u);
v___x_1043_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_isNone(v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
lean_inc(v___x_1043_);
v___x_1045_ = l_Lean_Syntax_matchesNull(v___x_1043_, v___x_664_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___x_1043_);
lean_dec(v_src_x3f_1041_);
lean_dec(v___y_1039_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1046_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1047_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1046_, v___y_1037_, v___y_1040_);
lean_dec(v_stx_530_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = l_Lean_Syntax_getArg(v___x_1043_, v___x_662_);
lean_dec(v___x_1043_);
v___x_1049_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120));
lean_inc(v___x_1048_);
v___x_1050_ = l_Lean_Syntax_isOfKind(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec(v___x_1048_);
lean_dec(v_src_x3f_1041_);
lean_dec(v___y_1039_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1051_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1052_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1051_, v___y_1037_, v___y_1040_);
lean_dec(v_stx_530_);
return v___x_1052_;
}
else
{
lean_object* v_opts_x3f_1053_; lean_object* v___x_1054_; 
lean_dec(v_stx_530_);
v_opts_x3f_1053_ = l_Lean_Syntax_getArg(v___x_1048_, v___x_664_);
lean_dec(v___x_1048_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_opts_x3f_1053_);
lean_inc_ref(v___y_1037_);
v___y_981_ = v___x_1042_;
v___y_982_ = v___y_1037_;
v___y_983_ = v___y_1038_;
v___y_984_ = v___y_1040_;
v___y_985_ = v___y_1039_;
v___y_986_ = v_src_x3f_1041_;
v_opts_x3f_987_ = v___x_1054_;
goto v___jp_980_;
}
}
}
else
{
lean_object* v___x_1055_; 
lean_dec(v___x_1043_);
lean_dec(v_stx_530_);
v___x_1055_ = lean_box(0);
lean_inc_ref(v___y_1037_);
v___y_981_ = v___x_1042_;
v___y_982_ = v___y_1037_;
v___y_983_ = v___y_1038_;
v___y_984_ = v___y_1040_;
v___y_985_ = v___y_1039_;
v___y_986_ = v_src_x3f_1041_;
v_opts_x3f_987_ = v___x_1055_;
goto v___jp_980_;
}
}
v___jp_1056_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_unsigned_to_nat(2u);
v___x_1061_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_isNone(v___x_1061_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; 
lean_inc(v___x_1061_);
v___x_1063_ = l_Lean_Syntax_matchesNull(v___x_1061_, v___x_664_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v___x_1061_);
lean_dec(v_ver_x3f_1057_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1064_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1065_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1064_, v___y_1058_, v___y_1059_);
lean_dec(v_stx_530_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = l_Lean_Syntax_getArg(v___x_1061_, v___x_662_);
lean_dec(v___x_1061_);
v___x_1067_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122));
lean_inc(v___x_1066_);
v___x_1068_ = l_Lean_Syntax_isOfKind(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v___x_1066_);
lean_dec(v_ver_x3f_1057_);
lean_dec(v___x_663_);
lean_dec(v_doc_x3f_531_);
v___x_1069_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1070_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_530_, v___x_1069_, v___y_1058_, v___y_1059_);
lean_dec(v_stx_530_);
return v___x_1070_;
}
else
{
lean_object* v_src_x3f_1071_; lean_object* v___x_1072_; 
v_src_x3f_1071_ = l_Lean_Syntax_getArg(v___x_1066_, v___x_664_);
lean_dec(v___x_1066_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_src_x3f_1071_);
v___y_1037_ = v___y_1058_;
v___y_1038_ = v___x_1060_;
v___y_1039_ = v_ver_x3f_1057_;
v___y_1040_ = v___y_1059_;
v_src_x3f_1041_ = v___x_1072_;
goto v___jp_1036_;
}
}
}
else
{
lean_object* v___x_1073_; 
lean_dec(v___x_1061_);
v___x_1073_ = lean_box(0);
v___y_1037_ = v___y_1058_;
v___y_1038_ = v___x_1060_;
v___y_1039_ = v_ver_x3f_1057_;
v___y_1040_ = v___y_1059_;
v_src_x3f_1041_ = v___x_1073_;
goto v___jp_1036_;
}
}
}
v___jp_534_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc(v___y_557_);
lean_inc(v___y_536_);
lean_inc(v___y_553_);
v___x_563_ = l_Lean_Syntax_node3(v___y_553_, v___y_559_, v___y_536_, v___y_557_, v___y_562_);
lean_inc_n(v___y_557_, 2);
lean_inc(v___y_542_);
lean_inc(v___y_553_);
v___x_564_ = l_Lean_Syntax_node3(v___y_553_, v___y_542_, v___y_557_, v___y_557_, v___x_563_);
lean_inc(v___y_553_);
v___x_565_ = l_Lean_Syntax_node2(v___y_553_, v___y_550_, v___y_551_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(10u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_array_push(v___x_567_, v___y_541_);
lean_inc(v___y_549_);
v___x_569_ = lean_array_push(v___x_568_, v___y_549_);
v___x_570_ = lean_array_push(v___x_569_, v___y_546_);
lean_inc(v___y_549_);
v___x_571_ = lean_array_push(v___x_570_, v___y_549_);
v___x_572_ = lean_array_push(v___x_571_, v___y_543_);
lean_inc(v___y_549_);
v___x_573_ = lean_array_push(v___x_572_, v___y_549_);
v___x_574_ = lean_array_push(v___x_573_, v___y_555_);
lean_inc(v___y_549_);
v___x_575_ = lean_array_push(v___x_574_, v___y_549_);
v___x_576_ = lean_array_push(v___x_575_, v___x_565_);
v___x_577_ = lean_array_push(v___x_576_, v___y_549_);
lean_inc(v___y_553_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___y_553_);
lean_ctor_set(v___x_578_, 1, v___y_542_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_inc(v___y_553_);
v___x_579_ = l_Lean_Syntax_node1(v___y_553_, v___y_548_, v___x_578_);
lean_inc_n(v___y_557_, 2);
lean_inc(v___y_553_);
v___x_580_ = l_Lean_Syntax_node6(v___y_553_, v___y_558_, v___y_544_, v___y_557_, v___x_579_, v___y_540_, v___y_557_, v___y_547_);
v___x_581_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0));
v___x_582_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1));
v___x_583_ = l_Lean_Name_mkStr4(v___y_545_, v___y_539_, v___x_581_, v___x_582_);
lean_inc_n(v___y_557_, 2);
lean_inc(v___y_553_);
v___x_584_ = l_Lean_Syntax_node2(v___y_553_, v___x_583_, v___y_557_, v___y_557_);
lean_inc(v___y_557_);
lean_inc(v___y_553_);
v___x_585_ = l_Lean_Syntax_node4(v___y_553_, v___y_560_, v___y_536_, v___x_580_, v___x_584_, v___y_557_);
lean_inc(v___y_553_);
v___x_586_ = l_Lean_Syntax_node5(v___y_553_, v___y_552_, v___y_561_, v___y_556_, v___y_538_, v___x_585_, v___y_557_);
v___x_587_ = l_Lean_Syntax_node2(v___y_553_, v___y_537_, v___y_554_, v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___y_535_);
return v___x_588_;
}
v___jp_589_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_inc(v___y_616_);
lean_inc(v___y_591_);
lean_inc(v___y_617_);
lean_inc(v___y_612_);
v___x_622_ = l_Lean_Syntax_node3(v___y_612_, v___y_617_, v___y_591_, v___y_616_, v___y_621_);
lean_inc_n(v___y_616_, 2);
lean_inc(v___y_602_);
lean_inc(v___y_612_);
v___x_623_ = l_Lean_Syntax_node3(v___y_612_, v___y_602_, v___y_616_, v___y_616_, v___x_622_);
lean_inc(v___y_610_);
lean_inc(v___y_612_);
v___x_624_ = l_Lean_Syntax_node2(v___y_612_, v___y_610_, v___y_599_, v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2));
lean_inc(v___y_612_);
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v___y_612_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4);
v___x_628_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5));
lean_inc(v___y_597_);
lean_inc(v___y_592_);
v___x_629_ = l_Lean_addMacroScope(v___y_592_, v___x_628_, v___y_597_);
lean_inc(v___y_609_);
lean_inc(v___y_612_);
v___x_630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_630_, 0, v___y_612_);
lean_ctor_set(v___x_630_, 1, v___x_627_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v___y_609_);
lean_inc(v___y_616_);
lean_inc(v___y_606_);
lean_inc(v___y_612_);
v___x_631_ = l_Lean_Syntax_node2(v___y_612_, v___y_606_, v___x_630_, v___y_616_);
lean_inc(v___y_616_);
lean_inc(v___y_591_);
lean_inc(v___y_617_);
lean_inc(v___y_612_);
v___x_632_ = l_Lean_Syntax_node3(v___y_612_, v___y_617_, v___y_591_, v___y_616_, v___y_601_);
lean_inc_n(v___y_616_, 2);
lean_inc(v___y_602_);
lean_inc(v___y_612_);
v___x_633_ = l_Lean_Syntax_node3(v___y_612_, v___y_602_, v___y_616_, v___y_616_, v___x_632_);
lean_inc(v___y_610_);
lean_inc(v___y_612_);
v___x_634_ = l_Lean_Syntax_node2(v___y_612_, v___y_610_, v___x_631_, v___x_633_);
v___x_635_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7);
v___x_636_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8));
lean_inc(v___y_597_);
lean_inc(v___y_592_);
v___x_637_ = l_Lean_addMacroScope(v___y_592_, v___x_636_, v___y_597_);
lean_inc(v___y_609_);
lean_inc(v___y_612_);
v___x_638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_638_, 0, v___y_612_);
lean_ctor_set(v___x_638_, 1, v___x_635_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_ctor_set(v___x_638_, 3, v___y_609_);
lean_inc(v___y_616_);
lean_inc(v___y_606_);
lean_inc(v___y_612_);
v___x_639_ = l_Lean_Syntax_node2(v___y_612_, v___y_606_, v___x_638_, v___y_616_);
lean_inc(v___y_616_);
lean_inc(v___y_591_);
lean_inc(v___y_617_);
lean_inc(v___y_612_);
v___x_640_ = l_Lean_Syntax_node3(v___y_612_, v___y_617_, v___y_591_, v___y_616_, v___y_603_);
lean_inc_n(v___y_616_, 2);
lean_inc(v___y_602_);
lean_inc(v___y_612_);
v___x_641_ = l_Lean_Syntax_node3(v___y_612_, v___y_602_, v___y_616_, v___y_616_, v___x_640_);
lean_inc(v___y_610_);
lean_inc(v___y_612_);
v___x_642_ = l_Lean_Syntax_node2(v___y_612_, v___y_610_, v___x_639_, v___x_641_);
v___x_643_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10);
v___x_644_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11));
lean_inc(v___y_597_);
lean_inc(v___y_592_);
v___x_645_ = l_Lean_addMacroScope(v___y_592_, v___x_644_, v___y_597_);
lean_inc(v___y_609_);
lean_inc(v___y_612_);
v___x_646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_646_, 0, v___y_612_);
lean_ctor_set(v___x_646_, 1, v___x_643_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
lean_ctor_set(v___x_646_, 3, v___y_609_);
lean_inc(v___y_616_);
lean_inc(v___y_606_);
lean_inc(v___y_612_);
v___x_647_ = l_Lean_Syntax_node2(v___y_612_, v___y_606_, v___x_646_, v___y_616_);
lean_inc(v___y_616_);
lean_inc(v___y_591_);
lean_inc(v___y_617_);
lean_inc(v___y_612_);
v___x_648_ = l_Lean_Syntax_node3(v___y_612_, v___y_617_, v___y_591_, v___y_616_, v___y_594_);
lean_inc_n(v___y_616_, 2);
lean_inc(v___y_602_);
lean_inc(v___y_612_);
v___x_649_ = l_Lean_Syntax_node3(v___y_612_, v___y_602_, v___y_616_, v___y_616_, v___x_648_);
lean_inc(v___y_610_);
lean_inc(v___y_612_);
v___x_650_ = l_Lean_Syntax_node2(v___y_612_, v___y_610_, v___x_647_, v___x_649_);
v___x_651_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13);
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14));
v___x_653_ = l_Lean_addMacroScope(v___y_592_, v___x_652_, v___y_597_);
lean_inc(v___y_612_);
v___x_654_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_654_, 0, v___y_612_);
lean_ctor_set(v___x_654_, 1, v___x_651_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
lean_ctor_set(v___x_654_, 3, v___y_609_);
lean_inc(v___y_616_);
lean_inc(v___y_612_);
v___x_655_ = l_Lean_Syntax_node2(v___y_612_, v___y_606_, v___x_654_, v___y_616_);
if (lean_obj_tag(v___y_619_) == 0)
{
v___y_535_ = v___y_590_;
v___y_536_ = v___y_591_;
v___y_537_ = v___y_593_;
v___y_538_ = v___y_595_;
v___y_539_ = v___y_596_;
v___y_540_ = v___y_598_;
v___y_541_ = v___x_624_;
v___y_542_ = v___y_602_;
v___y_543_ = v___x_642_;
v___y_544_ = v___y_604_;
v___y_545_ = v___y_605_;
v___y_546_ = v___x_634_;
v___y_547_ = v___y_607_;
v___y_548_ = v___y_608_;
v___y_549_ = v___x_626_;
v___y_550_ = v___y_610_;
v___y_551_ = v___x_655_;
v___y_552_ = v___y_611_;
v___y_553_ = v___y_612_;
v___y_554_ = v___y_613_;
v___y_555_ = v___x_650_;
v___y_556_ = v___y_614_;
v___y_557_ = v___y_616_;
v___y_558_ = v___y_615_;
v___y_559_ = v___y_617_;
v___y_560_ = v___y_618_;
v___y_561_ = v___y_620_;
v___y_562_ = v___y_600_;
goto v___jp_534_;
}
else
{
lean_object* v_val_656_; 
lean_dec(v___y_600_);
v_val_656_ = lean_ctor_get(v___y_619_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___y_619_);
v___y_535_ = v___y_590_;
v___y_536_ = v___y_591_;
v___y_537_ = v___y_593_;
v___y_538_ = v___y_595_;
v___y_539_ = v___y_596_;
v___y_540_ = v___y_598_;
v___y_541_ = v___x_624_;
v___y_542_ = v___y_602_;
v___y_543_ = v___x_642_;
v___y_544_ = v___y_604_;
v___y_545_ = v___y_605_;
v___y_546_ = v___x_634_;
v___y_547_ = v___y_607_;
v___y_548_ = v___y_608_;
v___y_549_ = v___x_626_;
v___y_550_ = v___y_610_;
v___y_551_ = v___x_655_;
v___y_552_ = v___y_611_;
v___y_553_ = v___y_612_;
v___y_554_ = v___y_613_;
v___y_555_ = v___x_650_;
v___y_556_ = v___y_614_;
v___y_557_ = v___y_616_;
v___y_558_ = v___y_615_;
v___y_559_ = v___y_617_;
v___y_560_ = v___y_618_;
v___y_561_ = v___y_620_;
v___y_562_ = v_val_656_;
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___boxed(lean_object* v_stx_1087_, lean_object* v_doc_x3f_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(v_stx_1087_, v_doc_x3f_1088_, v_a_1089_, v_a_1090_);
lean_dec_ref(v_a_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(lean_object* v_stx_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
lean_inc(v_stx_1098_);
v___x_1102_ = l_Lean_Syntax_isOfKind(v_stx_1098_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2));
v___x_1104_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1098_, v___x_1103_, v_a_1099_, v_a_1100_);
lean_dec(v_stx_1098_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_kw_1108_; lean_object* v___x_1109_; lean_object* v_spec_1110_; lean_object* v___y_1112_; lean_object* v___x_1140_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v_kw_1108_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1107_);
v___x_1109_ = lean_unsigned_to_nat(2u);
v_spec_1110_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1109_);
lean_dec(v_stx_1098_);
v___x_1140_ = l_Lean_Syntax_getOptional_x3f(v___x_1106_);
lean_dec(v___x_1106_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_box(0);
v___y_1112_ = v___x_1141_;
goto v___jp_1111_;
}
else
{
lean_object* v_val_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_val_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_val_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_val_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v___y_1112_ = v___x_1147_;
goto v___jp_1111_;
}
}
}
v___jp_1111_:
{
lean_object* v_methods_1113_; lean_object* v_quotContext_1114_; lean_object* v_currMacroScope_1115_; lean_object* v_currRecDepth_1116_; lean_object* v_maxRecDepth_1117_; lean_object* v_ref_1118_; lean_object* v_ref_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_methods_1113_ = lean_ctor_get(v_a_1099_, 0);
v_quotContext_1114_ = lean_ctor_get(v_a_1099_, 1);
v_currMacroScope_1115_ = lean_ctor_get(v_a_1099_, 2);
v_currRecDepth_1116_ = lean_ctor_get(v_a_1099_, 3);
v_maxRecDepth_1117_ = lean_ctor_get(v_a_1099_, 4);
v_ref_1118_ = lean_ctor_get(v_a_1099_, 5);
v_ref_1119_ = l_Lean_replaceRef(v_kw_1108_, v_ref_1118_);
lean_dec(v_kw_1108_);
lean_inc(v_maxRecDepth_1117_);
lean_inc(v_currRecDepth_1116_);
lean_inc(v_currMacroScope_1115_);
lean_inc(v_quotContext_1114_);
lean_inc(v_methods_1113_);
v___x_1120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1120_, 0, v_methods_1113_);
lean_ctor_set(v___x_1120_, 1, v_quotContext_1114_);
lean_ctor_set(v___x_1120_, 2, v_currMacroScope_1115_);
lean_ctor_set(v___x_1120_, 3, v_currRecDepth_1116_);
lean_ctor_set(v___x_1120_, 4, v_maxRecDepth_1117_);
lean_ctor_set(v___x_1120_, 5, v_ref_1119_);
v___x_1121_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(v_spec_1110_, v___y_1112_, v___x_1120_, v_a_1100_);
lean_dec_ref(v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_a_1123_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1122_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1131_ = lean_ctor_get(v___x_1121_, 0);
v_a_1132_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1121_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1131_);
lean_dec(v___x_1121_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed(lean_object* v_stx_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(v_stx_1150_, v_a_1151_, v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1(){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1182_ = l_Lean_Elab_macroAttribute;
v___x_1183_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
v___x_1184_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10));
v___x_1185_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed), 3, 0);
v___x_1186_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1182_, v___x_1183_, v___x_1184_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___boxed(lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
return v_res_1188_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Require(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Require(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Require(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Require(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Require(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Require(builtin);
}
#ifdef __cplusplus
}
#endif
