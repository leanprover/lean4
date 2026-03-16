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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
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
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 11, 239, 15, 0, 67, 249, 1)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ill-formed require syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "package_dep"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_value),LEAN_SCALAR_PTR_LITERAL(237, 25, 56, 91, 184, 179, 188, 66)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value;
static const lean_array_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dependency"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value),LEAN_SCALAR_PTR_LITERAL(248, 114, 43, 207, 103, 109, 40, 59)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value),LEAN_SCALAR_PTR_LITERAL(219, 110, 100, 210, 231, 203, 62, 196)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "src\?"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value),LEAN_SCALAR_PTR_LITERAL(34, 19, 24, 60, 150, 139, 215, 235)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "opts"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_value),LEAN_SCALAR_PTR_LITERAL(49, 15, 216, 57, 127, 228, 200, 93)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value;
static const lean_array_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value),LEAN_SCALAR_PTR_LITERAL(5, 204, 227, 250, 63, 151, 124, 47)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ill-formed version syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\"git#\""};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed name syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depName"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value),LEAN_SCALAR_PTR_LITERAL(11, 76, 0, 7, 47, 106, 167, 185)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromSource"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 246, 101, 8, 76, 68, 147)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fromGit"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value),LEAN_SCALAR_PTR_LITERAL(58, 198, 35, 138, 239, 183, 90, 121)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromPath"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value),LEAN_SCALAR_PTR_LITERAL(88, 231, 238, 12, 211, 124, 7, 152)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DependencySrc.path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 123, 123, 148, 32, 75, 229, 138)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value),LEAN_SCALAR_PTR_LITERAL(41, 247, 255, 238, 70, 62, 187, 2)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(203, 149, 114, 196, 65, 131, 70, 23)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value),LEAN_SCALAR_PTR_LITERAL(157, 188, 245, 236, 72, 147, 33, 123)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "withClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value),LEAN_SCALAR_PTR_LITERAL(62, 242, 50, 31, 135, 230, 200, 221)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value),LEAN_SCALAR_PTR_LITERAL(108, 123, 128, 15, 141, 170, 246, 11)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "verClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 66, 152, 98, 148, 165, 231)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "requireDecl"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 86, 225, 163, 119, 172, 216, 31)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed require declaration"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Require"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 32, 139, 116, 35, 151, 53, 69)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(239, 234, 19, 137, 104, 82, 181, 131)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 249, 219, 73, 145, 150, 211, 12)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 30, 72, 164, 69, 128, 229, 208)}};
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
v___x_208_ = l_Lean_addMacroScope(v___y_195_, v___x_207_, v___y_196_);
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
v___x_217_ = l_Lean_Syntax_node3(v___x_202_, v___x_216_, v___x_183_, v___y_197_, v_a_199_);
v___x_218_ = l_Lean_Syntax_node2(v___x_202_, v___x_203_, v___x_215_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_200_);
return v___x_219_;
}
v___jp_220_:
{
if (lean_obj_tag(v___y_221_) == 1)
{
lean_object* v_val_227_; lean_object* v_ref_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_val_227_ = lean_ctor_get(v___y_221_, 0);
lean_inc(v_val_227_);
lean_dec_ref(v___y_221_);
v_ref_228_ = l_Lean_replaceRef(v_val_227_, v___y_224_);
v___x_229_ = 0;
v___x_230_ = l_Lean_SourceInfo_fromRef(v_ref_228_, v___x_229_);
lean_dec(v_ref_228_);
v___x_231_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_232_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_233_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v___y_223_);
lean_inc(v___y_222_);
v___x_234_ = l_Lean_addMacroScope(v___y_222_, v___x_233_, v___y_223_);
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
v___y_195_ = v___y_222_;
v___y_196_ = v___y_223_;
v___y_197_ = v_a_225_;
v___y_198_ = v___y_224_;
v_a_199_ = v___x_239_;
v_a_200_ = v_a_226_;
goto v___jp_194_;
}
else
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___y_221_);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v___y_224_, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_243_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v___y_223_);
lean_inc(v___y_222_);
v___x_244_ = l_Lean_addMacroScope(v___y_222_, v___x_243_, v___y_223_);
v___x_245_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_246_, 0, v___x_241_);
lean_ctor_set(v___x_246_, 1, v___x_242_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v___x_245_);
v___y_195_ = v___y_222_;
v___y_196_ = v___y_223_;
v___y_197_ = v_a_225_;
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
v___y_221_ = v_subDir_x3f_248_;
v___y_222_ = v_quotContext_249_;
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
v___y_221_ = v_subDir_x3f_248_;
v___y_222_ = v_quotContext_249_;
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
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13));
v___x_312_ = l_String_toRawSubstring_x27(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25));
v___x_329_ = l_Lean_mkCIdent(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31));
v___x_336_ = l_String_toRawSubstring_x27(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36));
v___x_343_ = l_String_toRawSubstring_x27(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39));
v___x_348_ = l_String_toRawSubstring_x27(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42));
v___x_353_ = l_String_toRawSubstring_x27(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45));
v___x_358_ = l_String_toRawSubstring_x27(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Array_mkArray0(lean_box(0));
return v___x_375_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77));
v___x_427_ = l_String_toRawSubstring_x27(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107));
v___x_492_ = l_String_toRawSubstring_x27(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(lean_object* v_stx_527_, lean_object* v_doc_x3f_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2));
v___x_587_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5));
lean_inc(v_stx_527_);
v___x_588_ = l_Lean_Syntax_isOfKind(v_stx_527_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_doc_x3f_528_);
v___x_589_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_590_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_589_, v_a_529_, v_a_530_);
lean_dec(v_stx_527_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v_quotContext_724_; lean_object* v_currMacroScope_725_; lean_object* v_ref_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v_a_730_; lean_object* v_a_731_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v_ver_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v_a_897_; lean_object* v_a_898_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v_a_920_; lean_object* v_a_921_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v_opts_x3f_939_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v_src_x3f_993_; lean_object* v_ver_x3f_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_806_ = l_Lean_Syntax_getArg(v_stx_527_, v___x_591_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_1026_ = l_Lean_Syntax_getArg(v_stx_527_, v___x_807_);
v___x_1027_ = l_Lean_Syntax_isNone(v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
lean_inc(v___x_1026_);
v___x_1028_ = l_Lean_Syntax_matchesNull(v___x_1026_, v___x_807_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v___x_1026_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_1029_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_1030_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_1029_, v_a_529_, v_a_530_);
lean_dec(v_stx_527_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = l_Lean_Syntax_getArg(v___x_1026_, v___x_591_);
lean_dec(v___x_1026_);
v___x_1032_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121));
lean_inc(v___x_1031_);
v___x_1033_ = l_Lean_Syntax_isOfKind(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v___x_1031_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_1034_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_1035_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_1034_, v_a_529_, v_a_530_);
lean_dec(v_stx_527_);
return v___x_1035_;
}
else
{
lean_object* v_ver_x3f_1036_; lean_object* v___x_1037_; 
v_ver_x3f_1036_ = l_Lean_Syntax_getArg(v___x_1031_, v___x_807_);
lean_dec(v___x_1031_);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_ver_x3f_1036_);
v_ver_x3f_1009_ = v___x_1037_;
v___y_1010_ = v_a_529_;
v___y_1011_ = v_a_530_;
goto v___jp_1008_;
}
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v___x_1026_);
v___x_1038_ = lean_box(0);
v_ver_x3f_1009_ = v___x_1038_;
v___y_1010_ = v_a_529_;
v___y_1011_ = v_a_530_;
goto v___jp_1008_;
}
v___jp_592_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_619_ = l_Array_append___redArg(v___y_603_, v___y_618_);
lean_dec_ref(v___y_618_);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v___y_606_);
lean_ctor_set(v___x_620_, 1, v___y_614_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_622_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_621_);
v___x_623_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8));
lean_inc(v___y_606_);
v___x_624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_624_, 0, v___y_606_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_626_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_625_);
v___x_627_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_628_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_627_);
lean_inc(v___y_595_);
lean_inc(v___y_606_);
v___x_629_ = l_Lean_Syntax_node1(v___y_606_, v___x_628_, v___y_595_);
v___x_630_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11));
v___x_631_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12));
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_632_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___x_630_, v___x_631_);
v___x_633_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14);
v___x_634_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15));
lean_inc(v___y_617_);
lean_inc(v___y_610_);
v___x_635_ = l_Lean_addMacroScope(v___y_610_, v___x_634_, v___y_617_);
v___x_636_ = lean_box(0);
lean_inc(v___y_606_);
v___x_637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_637_, 0, v___y_606_);
lean_ctor_set(v___x_637_, 1, v___x_633_);
lean_ctor_set(v___x_637_, 2, v___x_635_);
lean_ctor_set(v___x_637_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___y_606_);
v___x_638_ = l_Lean_Syntax_node2(v___y_606_, v___x_632_, v___x_637_, v___y_595_);
lean_inc(v___y_606_);
v___x_639_ = l_Lean_Syntax_node2(v___y_606_, v___x_626_, v___x_629_, v___x_638_);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_640_ = l_Lean_Syntax_node1(v___y_606_, v___y_614_, v___x_639_);
v___x_641_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16));
lean_inc(v___y_606_);
v___x_642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_642_, 0, v___y_606_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_inc(v___y_606_);
v___x_643_ = l_Lean_Syntax_node3(v___y_606_, v___x_622_, v___x_624_, v___x_640_, v___x_642_);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_644_ = l_Lean_Syntax_node1(v___y_606_, v___y_614_, v___x_643_);
lean_inc_n(v___y_595_, 5);
lean_inc(v___y_606_);
v___x_645_ = l_Lean_Syntax_node7(v___y_606_, v___y_616_, v___x_620_, v___x_644_, v___y_595_, v___y_595_, v___y_595_, v___y_595_, v___y_595_);
v___x_646_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17));
lean_inc_ref(v___y_615_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_647_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_615_, v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18));
lean_inc(v___y_606_);
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_606_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
lean_inc_ref(v___y_615_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_651_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_615_, v___x_650_);
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20));
v___x_653_ = lean_box(2);
lean_inc(v___y_614_);
v___x_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___y_614_);
lean_ctor_set(v___x_654_, 2, v___x_652_);
v___x_655_ = lean_mk_empty_array_with_capacity(v___y_594_);
lean_inc(v___y_599_);
v___x_656_ = lean_array_push(v___x_655_, v___y_599_);
v___x_657_ = lean_array_push(v___x_656_, v___x_654_);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_653_);
lean_ctor_set(v___x_658_, 1, v___x_651_);
lean_ctor_set(v___x_658_, 2, v___x_657_);
v___x_659_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21));
lean_inc_ref(v___y_615_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_660_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_615_, v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_662_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23));
lean_inc(v___y_606_);
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_606_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26);
lean_inc(v___y_606_);
v___x_666_ = l_Lean_Syntax_node2(v___y_606_, v___x_662_, v___x_664_, v___x_665_);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_667_ = l_Lean_Syntax_node1(v___y_606_, v___y_614_, v___x_666_);
lean_inc(v___y_595_);
lean_inc(v___y_606_);
v___x_668_ = l_Lean_Syntax_node2(v___y_606_, v___x_660_, v___y_595_, v___x_667_);
v___x_669_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27));
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_670_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_615_, v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28));
lean_inc(v___y_606_);
v___x_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_606_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_674_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_673_);
v___x_675_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30));
lean_inc_ref(v___y_598_);
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_676_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_675_);
v___x_677_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32);
v___x_678_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33));
lean_inc(v___y_617_);
lean_inc(v___y_610_);
v___x_679_ = l_Lean_addMacroScope(v___y_610_, v___x_678_, v___y_617_);
lean_inc(v___y_606_);
v___x_680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_680_, 0, v___y_606_);
lean_ctor_set(v___x_680_, 1, v___x_677_);
lean_ctor_set(v___x_680_, 2, v___x_679_);
lean_ctor_set(v___x_680_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___x_676_);
lean_inc(v___y_606_);
v___x_681_ = l_Lean_Syntax_node2(v___y_606_, v___x_676_, v___x_680_, v___y_595_);
v___x_682_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34));
lean_inc_ref(v___y_608_);
lean_inc_ref(v___y_593_);
v___x_683_ = l_Lean_Name_mkStr4(v___y_593_, v___y_608_, v___y_598_, v___x_682_);
v___x_684_ = l_Lean_TSyntax_getId(v___y_599_);
lean_dec(v___y_599_);
v___x_685_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_684_);
lean_inc(v___y_595_);
lean_inc_ref(v___x_672_);
lean_inc(v___x_683_);
lean_inc(v___y_606_);
v___x_686_ = l_Lean_Syntax_node3(v___y_606_, v___x_683_, v___x_672_, v___y_595_, v___x_685_);
lean_inc_n(v___y_595_, 2);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_687_ = l_Lean_Syntax_node3(v___y_606_, v___y_614_, v___y_595_, v___y_595_, v___x_686_);
lean_inc(v___x_674_);
lean_inc(v___y_606_);
v___x_688_ = l_Lean_Syntax_node2(v___y_606_, v___x_674_, v___x_681_, v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35));
lean_inc(v___y_606_);
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v___y_606_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37);
v___x_692_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38));
lean_inc(v___y_617_);
lean_inc(v___y_610_);
v___x_693_ = l_Lean_addMacroScope(v___y_610_, v___x_692_, v___y_617_);
lean_inc(v___y_606_);
v___x_694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_694_, 0, v___y_606_);
lean_ctor_set(v___x_694_, 1, v___x_691_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
lean_ctor_set(v___x_694_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___x_676_);
lean_inc(v___y_606_);
v___x_695_ = l_Lean_Syntax_node2(v___y_606_, v___x_676_, v___x_694_, v___y_595_);
lean_inc(v___y_595_);
lean_inc_ref(v___x_672_);
lean_inc(v___x_683_);
lean_inc(v___y_606_);
v___x_696_ = l_Lean_Syntax_node3(v___y_606_, v___x_683_, v___x_672_, v___y_595_, v___y_597_);
lean_inc_n(v___y_595_, 2);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_697_ = l_Lean_Syntax_node3(v___y_606_, v___y_614_, v___y_595_, v___y_595_, v___x_696_);
lean_inc(v___x_674_);
lean_inc(v___y_606_);
v___x_698_ = l_Lean_Syntax_node2(v___y_606_, v___x_674_, v___x_695_, v___x_697_);
v___x_699_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40);
v___x_700_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41));
lean_inc(v___y_617_);
lean_inc(v___y_610_);
v___x_701_ = l_Lean_addMacroScope(v___y_610_, v___x_700_, v___y_617_);
lean_inc(v___y_606_);
v___x_702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_702_, 0, v___y_606_);
lean_ctor_set(v___x_702_, 1, v___x_699_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
lean_ctor_set(v___x_702_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___x_676_);
lean_inc(v___y_606_);
v___x_703_ = l_Lean_Syntax_node2(v___y_606_, v___x_676_, v___x_702_, v___y_595_);
lean_inc(v___y_595_);
lean_inc_ref(v___x_672_);
lean_inc(v___x_683_);
lean_inc(v___y_606_);
v___x_704_ = l_Lean_Syntax_node3(v___y_606_, v___x_683_, v___x_672_, v___y_595_, v___y_611_);
lean_inc_n(v___y_595_, 2);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_705_ = l_Lean_Syntax_node3(v___y_606_, v___y_614_, v___y_595_, v___y_595_, v___x_704_);
lean_inc(v___x_674_);
lean_inc(v___y_606_);
v___x_706_ = l_Lean_Syntax_node2(v___y_606_, v___x_674_, v___x_703_, v___x_705_);
v___x_707_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43);
v___x_708_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44));
lean_inc(v___y_617_);
lean_inc(v___y_610_);
v___x_709_ = l_Lean_addMacroScope(v___y_610_, v___x_708_, v___y_617_);
lean_inc(v___y_606_);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___y_606_);
lean_ctor_set(v___x_710_, 1, v___x_707_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
lean_ctor_set(v___x_710_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___x_676_);
lean_inc(v___y_606_);
v___x_711_ = l_Lean_Syntax_node2(v___y_606_, v___x_676_, v___x_710_, v___y_595_);
lean_inc(v___y_595_);
lean_inc_ref(v___x_672_);
lean_inc(v___x_683_);
lean_inc(v___y_606_);
v___x_712_ = l_Lean_Syntax_node3(v___y_606_, v___x_683_, v___x_672_, v___y_595_, v___y_613_);
lean_inc_n(v___y_595_, 2);
lean_inc(v___y_614_);
lean_inc(v___y_606_);
v___x_713_ = l_Lean_Syntax_node3(v___y_606_, v___y_614_, v___y_595_, v___y_595_, v___x_712_);
lean_inc(v___x_674_);
lean_inc(v___y_606_);
v___x_714_ = l_Lean_Syntax_node2(v___y_606_, v___x_674_, v___x_711_, v___x_713_);
v___x_715_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46);
v___x_716_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47));
v___x_717_ = l_Lean_addMacroScope(v___y_610_, v___x_716_, v___y_617_);
lean_inc(v___y_606_);
v___x_718_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_718_, 0, v___y_606_);
lean_ctor_set(v___x_718_, 1, v___x_715_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
lean_ctor_set(v___x_718_, 3, v___x_636_);
lean_inc(v___y_595_);
lean_inc(v___y_606_);
v___x_719_ = l_Lean_Syntax_node2(v___y_606_, v___x_676_, v___x_718_, v___y_595_);
if (lean_obj_tag(v___y_601_) == 0)
{
v___y_532_ = v___x_706_;
v___y_533_ = v___y_593_;
v___y_534_ = v___x_690_;
v___y_535_ = v___y_595_;
v___y_536_ = v___y_596_;
v___y_537_ = v___x_658_;
v___y_538_ = v___x_714_;
v___y_539_ = v___x_688_;
v___y_540_ = v___x_719_;
v___y_541_ = v___x_672_;
v___y_542_ = v___x_649_;
v___y_543_ = v___y_600_;
v___y_544_ = v___y_602_;
v___y_545_ = v___y_604_;
v___y_546_ = v___y_605_;
v___y_547_ = v___x_674_;
v___y_548_ = v___y_606_;
v___y_549_ = v___x_645_;
v___y_550_ = v___y_607_;
v___y_551_ = v___x_647_;
v___y_552_ = v___y_608_;
v___y_553_ = v___x_670_;
v___y_554_ = v___x_698_;
v___y_555_ = v___y_612_;
v___y_556_ = v___y_614_;
v___y_557_ = v___x_683_;
v___y_558_ = v___x_668_;
v___y_559_ = v___y_609_;
goto v___jp_531_;
}
else
{
lean_object* v_val_720_; 
lean_dec(v___y_609_);
v_val_720_ = lean_ctor_get(v___y_601_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v___y_601_);
v___y_532_ = v___x_706_;
v___y_533_ = v___y_593_;
v___y_534_ = v___x_690_;
v___y_535_ = v___y_595_;
v___y_536_ = v___y_596_;
v___y_537_ = v___x_658_;
v___y_538_ = v___x_714_;
v___y_539_ = v___x_688_;
v___y_540_ = v___x_719_;
v___y_541_ = v___x_672_;
v___y_542_ = v___x_649_;
v___y_543_ = v___y_600_;
v___y_544_ = v___y_602_;
v___y_545_ = v___y_604_;
v___y_546_ = v___y_605_;
v___y_547_ = v___x_674_;
v___y_548_ = v___y_606_;
v___y_549_ = v___x_645_;
v___y_550_ = v___y_607_;
v___y_551_ = v___x_647_;
v___y_552_ = v___y_608_;
v___y_553_ = v___x_670_;
v___y_554_ = v___x_698_;
v___y_555_ = v___y_612_;
v___y_556_ = v___y_614_;
v___y_557_ = v___x_683_;
v___y_558_ = v___x_668_;
v___y_559_ = v_val_720_;
goto v___jp_531_;
}
}
v___jp_721_:
{
uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_732_ = 0;
v___x_733_ = l_Lean_SourceInfo_fromRef(v_ref_726_, v___x_732_);
lean_dec(v_ref_726_);
v___x_734_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49));
v___x_735_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51));
v___x_736_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52));
lean_inc(v___x_733_);
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_733_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53));
lean_inc(v___x_733_);
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_733_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc_ref(v___x_739_);
lean_inc_ref(v___x_737_);
lean_inc(v___x_733_);
v___x_740_ = l_Lean_Syntax_node2(v___x_733_, v___x_735_, v___x_737_, v___x_739_);
v___x_741_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0));
v___x_742_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1));
v___x_743_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2));
v___x_744_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55));
v___x_745_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_746_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56);
lean_inc(v___x_733_);
v___x_747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_747_, 0, v___x_733_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58));
lean_inc_ref(v___x_747_);
lean_inc(v___x_733_);
v___x_749_ = l_Lean_Syntax_node1(v___x_733_, v___x_748_, v___x_747_);
v___x_750_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60));
lean_inc_ref(v___x_747_);
lean_inc(v___x_733_);
v___x_751_ = l_Lean_Syntax_node1(v___x_733_, v___x_750_, v___x_747_);
lean_inc_ref(v___x_739_);
lean_inc(v___x_751_);
lean_inc_ref_n(v___x_747_, 2);
lean_inc_ref(v___x_737_);
lean_inc(v___x_733_);
v___x_752_ = l_Lean_Syntax_node6(v___x_733_, v___x_744_, v___x_737_, v___x_747_, v___x_749_, v___x_751_, v___x_747_, v___x_739_);
lean_inc(v___x_733_);
v___x_753_ = l_Lean_Syntax_node2(v___x_733_, v___x_734_, v___x_740_, v___x_752_);
v___x_754_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61));
v___x_755_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63));
v___x_756_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65));
if (lean_obj_tag(v_doc_x3f_528_) == 1)
{
lean_object* v_val_757_; lean_object* v___x_758_; 
v_val_757_ = lean_ctor_get(v_doc_x3f_528_, 0);
lean_inc(v_val_757_);
lean_dec_ref(v_doc_x3f_528_);
v___x_758_ = l_Array_mkArray1___redArg(v_val_757_);
v___y_593_ = v___x_741_;
v___y_594_ = v___y_727_;
v___y_595_ = v___x_747_;
v___y_596_ = v___x_751_;
v___y_597_ = v___y_728_;
v___y_598_ = v___x_743_;
v___y_599_ = v___y_723_;
v___y_600_ = v___x_748_;
v___y_601_ = v___y_722_;
v___y_602_ = v_a_731_;
v___y_603_ = v___x_746_;
v___y_604_ = v___x_739_;
v___y_605_ = v___x_755_;
v___y_606_ = v___x_733_;
v___y_607_ = v___x_744_;
v___y_608_ = v___x_742_;
v___y_609_ = v___x_753_;
v___y_610_ = v_quotContext_724_;
v___y_611_ = v___y_729_;
v___y_612_ = v___x_737_;
v___y_613_ = v_a_730_;
v___y_614_ = v___x_745_;
v___y_615_ = v___x_754_;
v___y_616_ = v___x_756_;
v___y_617_ = v_currMacroScope_725_;
v___y_618_ = v___x_758_;
goto v___jp_592_;
}
else
{
lean_object* v___x_759_; 
lean_dec(v_doc_x3f_528_);
v___x_759_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66));
v___y_593_ = v___x_741_;
v___y_594_ = v___y_727_;
v___y_595_ = v___x_747_;
v___y_596_ = v___x_751_;
v___y_597_ = v___y_728_;
v___y_598_ = v___x_743_;
v___y_599_ = v___y_723_;
v___y_600_ = v___x_748_;
v___y_601_ = v___y_722_;
v___y_602_ = v_a_731_;
v___y_603_ = v___x_746_;
v___y_604_ = v___x_739_;
v___y_605_ = v___x_755_;
v___y_606_ = v___x_733_;
v___y_607_ = v___x_744_;
v___y_608_ = v___x_742_;
v___y_609_ = v___x_753_;
v___y_610_ = v_quotContext_724_;
v___y_611_ = v___y_729_;
v___y_612_ = v___x_737_;
v___y_613_ = v_a_730_;
v___y_614_ = v___x_745_;
v___y_615_ = v___x_754_;
v___y_616_ = v___x_756_;
v___y_617_ = v_currMacroScope_725_;
v___y_618_ = v___x_759_;
goto v___jp_592_;
}
}
v___jp_760_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_764_);
if (lean_obj_tag(v___y_761_) == 1)
{
lean_object* v_val_770_; lean_object* v_quotContext_771_; lean_object* v_currMacroScope_772_; lean_object* v_ref_773_; lean_object* v_ref_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_val_770_ = lean_ctor_get(v___y_761_, 0);
lean_inc(v_val_770_);
lean_dec_ref(v___y_761_);
v_quotContext_771_ = lean_ctor_get(v___y_767_, 1);
lean_inc(v_quotContext_771_);
v_currMacroScope_772_ = lean_ctor_get(v___y_767_, 2);
lean_inc(v_currMacroScope_772_);
v_ref_773_ = lean_ctor_get(v___y_767_, 5);
lean_inc(v_ref_773_);
lean_dec_ref(v___y_767_);
v_ref_774_ = l_Lean_replaceRef(v_val_770_, v_ref_773_);
v___x_775_ = 0;
v___x_776_ = l_Lean_SourceInfo_fromRef(v_ref_774_, v___x_775_);
lean_dec(v_ref_774_);
v___x_777_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_778_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_779_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_772_);
lean_inc(v_quotContext_771_);
v___x_780_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_779_, v_currMacroScope_772_);
v___x_781_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_776_);
v___x_782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_782_, 0, v___x_776_);
lean_ctor_set(v___x_782_, 1, v___x_778_);
lean_ctor_set(v___x_782_, 2, v___x_780_);
lean_ctor_set(v___x_782_, 3, v___x_781_);
v___x_783_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_776_);
v___x_784_ = l_Lean_Syntax_node1(v___x_776_, v___x_783_, v_val_770_);
v___x_785_ = l_Lean_Syntax_node2(v___x_776_, v___x_777_, v___x_782_, v___x_784_);
v___y_722_ = v___y_762_;
v___y_723_ = v___x_769_;
v_quotContext_724_ = v_quotContext_771_;
v_currMacroScope_725_ = v_currMacroScope_772_;
v_ref_726_ = v_ref_773_;
v___y_727_ = v___y_763_;
v___y_728_ = v___y_765_;
v___y_729_ = v_ver_766_;
v_a_730_ = v___x_785_;
v_a_731_ = v___y_768_;
goto v___jp_721_;
}
else
{
lean_object* v_quotContext_786_; lean_object* v_currMacroScope_787_; lean_object* v_ref_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___y_761_);
v_quotContext_786_ = lean_ctor_get(v___y_767_, 1);
lean_inc(v_quotContext_786_);
v_currMacroScope_787_ = lean_ctor_get(v___y_767_, 2);
lean_inc(v_currMacroScope_787_);
v_ref_788_ = lean_ctor_get(v___y_767_, 5);
lean_inc(v_ref_788_);
lean_dec_ref(v___y_767_);
v___x_789_ = 0;
v___x_790_ = l_Lean_SourceInfo_fromRef(v_ref_788_, v___x_789_);
v___x_791_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_792_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v_currMacroScope_787_);
lean_inc(v_quotContext_786_);
v___x_793_ = l_Lean_addMacroScope(v_quotContext_786_, v___x_792_, v_currMacroScope_787_);
v___x_794_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_795_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_790_);
lean_ctor_set(v___x_795_, 1, v___x_791_);
lean_ctor_set(v___x_795_, 2, v___x_793_);
lean_ctor_set(v___x_795_, 3, v___x_794_);
v___y_722_ = v___y_762_;
v___y_723_ = v___x_769_;
v_quotContext_724_ = v_quotContext_786_;
v_currMacroScope_725_ = v_currMacroScope_787_;
v_ref_726_ = v_ref_788_;
v___y_727_ = v___y_763_;
v___y_728_ = v___y_765_;
v___y_729_ = v_ver_766_;
v_a_730_ = v___x_795_;
v_a_731_ = v___y_768_;
goto v___jp_721_;
}
}
v___jp_796_:
{
if (lean_obj_tag(v___y_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_a_805_; 
v_a_804_ = lean_ctor_get(v___y_803_, 0);
lean_inc(v_a_804_);
v_a_805_ = lean_ctor_get(v___y_803_, 1);
lean_inc(v_a_805_);
lean_dec_ref(v___y_803_);
v___y_761_ = v___y_798_;
v___y_762_ = v___y_797_;
v___y_763_ = v___y_799_;
v___y_764_ = v___y_800_;
v___y_765_ = v___y_802_;
v_ver_766_ = v_a_804_;
v___y_767_ = v___y_801_;
v___y_768_ = v_a_805_;
goto v___jp_760_;
}
else
{
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v_doc_x3f_528_);
return v___y_803_;
}
}
v___jp_808_:
{
if (lean_obj_tag(v___y_809_) == 1)
{
lean_object* v_val_817_; lean_object* v_methods_818_; lean_object* v_quotContext_819_; lean_object* v_currMacroScope_820_; lean_object* v_currRecDepth_821_; lean_object* v_maxRecDepth_822_; lean_object* v_ref_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v_ref_826_; lean_object* v___x_827_; 
v_val_817_ = lean_ctor_get(v___y_809_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v___y_809_);
v_methods_818_ = lean_ctor_get(v___y_813_, 0);
v_quotContext_819_ = lean_ctor_get(v___y_813_, 1);
v_currMacroScope_820_ = lean_ctor_get(v___y_813_, 2);
v_currRecDepth_821_ = lean_ctor_get(v___y_813_, 3);
v_maxRecDepth_822_ = lean_ctor_get(v___y_813_, 4);
v_ref_823_ = lean_ctor_get(v___y_813_, 5);
v___x_824_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68));
lean_inc(v_val_817_);
v___x_825_ = l_Lean_Syntax_isOfKind(v_val_817_, v___x_824_);
v_ref_826_ = l_Lean_replaceRef(v_val_817_, v_ref_823_);
lean_inc(v_ref_826_);
lean_inc(v_maxRecDepth_822_);
lean_inc(v_currRecDepth_821_);
lean_inc(v_currMacroScope_820_);
lean_inc(v_quotContext_819_);
lean_inc(v_methods_818_);
v___x_827_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_827_, 0, v_methods_818_);
lean_ctor_set(v___x_827_, 1, v_quotContext_819_);
lean_ctor_set(v___x_827_, 2, v_currMacroScope_820_);
lean_ctor_set(v___x_827_, 3, v_currRecDepth_821_);
lean_ctor_set(v___x_827_, 4, v_maxRecDepth_822_);
lean_ctor_set(v___x_827_, 5, v_ref_826_);
if (v___x_825_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_ref_826_);
v___x_828_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69));
v___x_829_ = l_Lean_Macro_throwErrorAt___redArg(v_val_817_, v___x_828_, v___x_827_, v___y_815_);
lean_dec(v_val_817_);
v___y_797_ = v___y_810_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_814_;
v___y_801_ = v___y_813_;
v___y_802_ = v___y_816_;
v___y_803_ = v___x_829_;
goto v___jp_796_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = l_Lean_Syntax_getArg(v_val_817_, v___x_591_);
lean_inc(v___x_830_);
v___x_831_ = l_Lean_Syntax_matchesNull(v___x_830_, v___x_807_);
if (v___x_831_ == 0)
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_Syntax_matchesNull(v___x_830_, v___x_591_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_ref_826_);
v___x_833_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69));
v___x_834_ = l_Lean_Macro_throwErrorAt___redArg(v_val_817_, v___x_833_, v___x_827_, v___y_815_);
lean_dec(v_val_817_);
v___y_797_ = v___y_810_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_814_;
v___y_801_ = v___y_813_;
v___y_802_ = v___y_816_;
v___y_803_ = v___x_834_;
goto v___jp_796_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v___x_827_);
v___x_835_ = l_Lean_Syntax_getArg(v_val_817_, v___x_807_);
lean_dec(v_val_817_);
v___x_836_ = l_Lean_SourceInfo_fromRef(v_ref_826_, v___x_831_);
lean_dec(v_ref_826_);
v___x_837_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_838_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_839_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_820_);
lean_inc(v_quotContext_819_);
v___x_840_ = l_Lean_addMacroScope(v_quotContext_819_, v___x_839_, v_currMacroScope_820_);
v___x_841_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_836_);
v___x_842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_842_, 0, v___x_836_);
lean_ctor_set(v___x_842_, 1, v___x_838_);
lean_ctor_set(v___x_842_, 2, v___x_840_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
v___x_843_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_836_);
v___x_844_ = l_Lean_Syntax_node1(v___x_836_, v___x_843_, v___x_835_);
v___x_845_ = l_Lean_Syntax_node2(v___x_836_, v___x_837_, v___x_842_, v___x_844_);
v___y_761_ = v___y_811_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_812_;
v___y_764_ = v___y_814_;
v___y_765_ = v___y_816_;
v_ver_766_ = v___x_845_;
v___y_767_ = v___y_813_;
v___y_768_ = v___y_815_;
goto v___jp_760_;
}
}
else
{
lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v___x_830_);
lean_dec_ref(v___x_827_);
v___x_846_ = l_Lean_Syntax_getArg(v_val_817_, v___x_807_);
lean_dec(v_val_817_);
v___x_847_ = 0;
v___x_848_ = l_Lean_SourceInfo_fromRef(v_ref_826_, v___x_847_);
lean_dec(v_ref_826_);
v___x_849_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_850_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_851_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_820_);
lean_inc(v_quotContext_819_);
v___x_852_ = l_Lean_addMacroScope(v_quotContext_819_, v___x_851_, v_currMacroScope_820_);
v___x_853_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc(v___x_848_);
v___x_854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_854_, 0, v___x_848_);
lean_ctor_set(v___x_854_, 1, v___x_850_);
lean_ctor_set(v___x_854_, 2, v___x_852_);
lean_ctor_set(v___x_854_, 3, v___x_853_);
v___x_855_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_856_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71));
v___x_857_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73));
v___x_858_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74));
lean_inc(v___x_848_);
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_848_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76));
v___x_861_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78);
v___x_862_ = lean_box(0);
lean_inc(v_currMacroScope_820_);
lean_inc(v_quotContext_819_);
v___x_863_ = l_Lean_addMacroScope(v_quotContext_819_, v___x_862_, v_currMacroScope_820_);
v___x_864_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90));
lean_inc(v___x_848_);
v___x_865_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_865_, 0, v___x_848_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
lean_ctor_set(v___x_865_, 2, v___x_863_);
lean_ctor_set(v___x_865_, 3, v___x_864_);
lean_inc(v___x_848_);
v___x_866_ = l_Lean_Syntax_node1(v___x_848_, v___x_860_, v___x_865_);
lean_inc(v___x_848_);
v___x_867_ = l_Lean_Syntax_node2(v___x_848_, v___x_857_, v___x_859_, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92));
v___x_869_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94));
v___x_870_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95));
lean_inc(v___x_848_);
v___x_871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_848_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_inc(v___x_848_);
v___x_872_ = l_Lean_Syntax_node1(v___x_848_, v___x_869_, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96));
lean_inc(v___x_848_);
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_848_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
lean_inc(v___x_848_);
v___x_875_ = l_Lean_Syntax_node3(v___x_848_, v___x_868_, v___x_872_, v___x_874_, v___x_846_);
v___x_876_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97));
lean_inc(v___x_848_);
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_848_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
lean_inc(v___x_848_);
v___x_878_ = l_Lean_Syntax_node3(v___x_848_, v___x_856_, v___x_867_, v___x_875_, v___x_877_);
lean_inc(v___x_848_);
v___x_879_ = l_Lean_Syntax_node1(v___x_848_, v___x_855_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node2(v___x_848_, v___x_849_, v___x_854_, v___x_879_);
v___y_761_ = v___y_811_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_812_;
v___y_764_ = v___y_814_;
v___y_765_ = v___y_816_;
v_ver_766_ = v___x_880_;
v___y_767_ = v___y_813_;
v___y_768_ = v___y_815_;
goto v___jp_760_;
}
}
}
else
{
lean_object* v_quotContext_881_; lean_object* v_currMacroScope_882_; lean_object* v_ref_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v___y_809_);
v_quotContext_881_ = lean_ctor_get(v___y_813_, 1);
v_currMacroScope_882_ = lean_ctor_get(v___y_813_, 2);
v_ref_883_ = lean_ctor_get(v___y_813_, 5);
v___x_884_ = 0;
v___x_885_ = l_Lean_SourceInfo_fromRef(v_ref_883_, v___x_884_);
v___x_886_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_887_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v_currMacroScope_882_);
lean_inc(v_quotContext_881_);
v___x_888_ = l_Lean_addMacroScope(v_quotContext_881_, v___x_887_, v_currMacroScope_882_);
v___x_889_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_890_, 0, v___x_885_);
lean_ctor_set(v___x_890_, 1, v___x_886_);
lean_ctor_set(v___x_890_, 2, v___x_888_);
lean_ctor_set(v___x_890_, 3, v___x_889_);
v___y_761_ = v___y_811_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_812_;
v___y_764_ = v___y_814_;
v___y_765_ = v___y_816_;
v_ver_766_ = v___x_890_;
v___y_767_ = v___y_813_;
v___y_768_ = v___y_815_;
goto v___jp_760_;
}
}
v___jp_891_:
{
uint8_t v___x_899_; 
lean_inc(v___x_806_);
v___x_899_ = l_Lean_Syntax_isOfKind(v___x_806_, v___y_894_);
lean_dec(v___y_894_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_a_897_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v_doc_x3f_528_);
v___x_900_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98));
v___x_901_ = l_Lean_Macro_throwErrorAt___redArg(v___x_806_, v___x_900_, v___y_895_, v_a_898_);
lean_dec(v___x_806_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = l_Lean_Syntax_getArg(v___x_806_, v___x_591_);
v___x_903_ = l_Lean_Syntax_isNone(v___x_902_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
lean_inc(v___x_902_);
v___x_904_ = l_Lean_Syntax_matchesNull(v___x_902_, v___y_896_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v___x_902_);
lean_dec(v_a_897_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v_doc_x3f_528_);
v___x_905_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98));
v___x_906_ = l_Lean_Macro_throwErrorAt___redArg(v___x_806_, v___x_905_, v___y_895_, v_a_898_);
lean_dec(v___x_806_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = l_Lean_Syntax_getArg(v___x_902_, v___x_591_);
lean_dec(v___x_902_);
v___x_908_ = l_Lean_Syntax_getArg(v___x_806_, v___x_807_);
lean_dec(v___x_806_);
v___y_809_ = v___y_892_;
v___y_810_ = v___y_893_;
v___y_811_ = v_a_897_;
v___y_812_ = v___y_896_;
v___y_813_ = v___y_895_;
v___y_814_ = v___x_908_;
v___y_815_ = v_a_898_;
v___y_816_ = v___x_907_;
goto v___jp_808_;
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v___x_902_);
v___x_909_ = l_Lean_Syntax_getArg(v___x_806_, v___x_807_);
v___x_910_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77));
v___x_911_ = 0;
v___x_912_ = l_Lean_SourceInfo_fromRef(v___x_806_, v___x_911_);
lean_dec(v___x_806_);
v___x_913_ = l_Lean_Syntax_mkStrLit(v___x_910_, v___x_912_);
v___y_809_ = v___y_892_;
v___y_810_ = v___y_893_;
v___y_811_ = v_a_897_;
v___y_812_ = v___y_896_;
v___y_813_ = v___y_895_;
v___y_814_ = v___x_909_;
v___y_815_ = v_a_898_;
v___y_816_ = v___x_913_;
goto v___jp_808_;
}
}
}
v___jp_914_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v_a_920_);
v___y_892_ = v___y_916_;
v___y_893_ = v___y_915_;
v___y_894_ = v___y_917_;
v___y_895_ = v___y_919_;
v___y_896_ = v___y_918_;
v_a_897_ = v___x_922_;
v_a_898_ = v_a_921_;
goto v___jp_891_;
}
v___jp_923_:
{
if (lean_obj_tag(v___y_929_) == 0)
{
lean_object* v_a_930_; lean_object* v_a_931_; 
v_a_930_ = lean_ctor_get(v___y_929_, 0);
lean_inc(v_a_930_);
v_a_931_ = lean_ctor_get(v___y_929_, 1);
lean_inc(v_a_931_);
lean_dec_ref(v___y_929_);
v___y_915_ = v___y_925_;
v___y_916_ = v___y_924_;
v___y_917_ = v___y_926_;
v___y_918_ = v___y_928_;
v___y_919_ = v___y_927_;
v_a_920_ = v_a_930_;
v_a_921_ = v_a_931_;
goto v___jp_914_;
}
else
{
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
return v___y_929_;
}
}
v___jp_932_:
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100));
if (lean_obj_tag(v___y_938_) == 0)
{
v___y_892_ = v___y_934_;
v___y_893_ = v_opts_x3f_939_;
v___y_894_ = v___x_940_;
v___y_895_ = v___y_933_;
v___y_896_ = v___y_937_;
v_a_897_ = v___y_938_;
v_a_898_ = v___y_936_;
goto v___jp_891_;
}
else
{
lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_987_; 
v_val_941_ = lean_ctor_get(v___y_938_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___y_938_);
if (v_isSharedCheck_987_ == 0)
{
v___x_943_ = v___y_938_;
v_isShared_944_ = v_isSharedCheck_987_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_dec(v___y_938_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_987_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102));
lean_inc(v_val_941_);
v___x_946_ = l_Lean_Syntax_isOfKind(v_val_941_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_del_object(v___x_943_);
v___x_947_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
lean_inc_ref(v___y_933_);
v___x_948_ = l_Lean_Macro_throwErrorAt___redArg(v_val_941_, v___x_947_, v___y_933_, v___y_936_);
lean_dec(v_val_941_);
v___y_924_ = v___y_934_;
v___y_925_ = v_opts_x3f_939_;
v___y_926_ = v___x_940_;
v___y_927_ = v___y_933_;
v___y_928_ = v___y_937_;
v___y_929_ = v___x_948_;
goto v___jp_923_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = l_Lean_Syntax_getArg(v_val_941_, v___x_591_);
v___x_950_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104));
lean_inc(v___x_949_);
v___x_951_ = l_Lean_Syntax_isOfKind(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; uint8_t v___x_953_; 
lean_del_object(v___x_943_);
v___x_952_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106));
lean_inc(v___x_949_);
v___x_953_ = l_Lean_Syntax_isOfKind(v___x_949_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v___x_949_);
v___x_954_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
lean_inc_ref(v___y_933_);
v___x_955_ = l_Lean_Macro_throwErrorAt___redArg(v_val_941_, v___x_954_, v___y_933_, v___y_936_);
lean_dec(v_val_941_);
v___y_924_ = v___y_934_;
v___y_925_ = v_opts_x3f_939_;
v___y_926_ = v___x_940_;
v___y_927_ = v___y_933_;
v___y_928_ = v___y_937_;
v___y_929_ = v___x_955_;
goto v___jp_923_;
}
else
{
lean_object* v_quotContext_956_; lean_object* v_currMacroScope_957_; lean_object* v_ref_958_; lean_object* v___x_959_; lean_object* v_ref_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_quotContext_956_ = lean_ctor_get(v___y_933_, 1);
v_currMacroScope_957_ = lean_ctor_get(v___y_933_, 2);
v_ref_958_ = lean_ctor_get(v___y_933_, 5);
v___x_959_ = l_Lean_Syntax_getArg(v___x_949_, v___x_591_);
lean_dec(v___x_949_);
v_ref_960_ = l_Lean_replaceRef(v_val_941_, v_ref_958_);
lean_dec(v_val_941_);
v___x_961_ = l_Lean_SourceInfo_fromRef(v_ref_960_, v___x_951_);
lean_dec(v_ref_960_);
v___x_962_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_963_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108);
v___x_964_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110));
lean_inc(v_currMacroScope_957_);
lean_inc(v_quotContext_956_);
v___x_965_ = l_Lean_addMacroScope(v_quotContext_956_, v___x_964_, v_currMacroScope_957_);
v___x_966_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115));
lean_inc(v___x_961_);
v___x_967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_967_, 0, v___x_961_);
lean_ctor_set(v___x_967_, 1, v___x_963_);
lean_ctor_set(v___x_967_, 2, v___x_965_);
lean_ctor_set(v___x_967_, 3, v___x_966_);
v___x_968_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
lean_inc(v___x_961_);
v___x_969_ = l_Lean_Syntax_node1(v___x_961_, v___x_968_, v___x_959_);
v___x_970_ = l_Lean_Syntax_node2(v___x_961_, v___x_962_, v___x_967_, v___x_969_);
v___y_915_ = v_opts_x3f_939_;
v___y_916_ = v___y_934_;
v___y_917_ = v___x_940_;
v___y_918_ = v___y_937_;
v___y_919_ = v___y_933_;
v_a_920_ = v___x_970_;
v_a_921_ = v___y_936_;
goto v___jp_914_;
}
}
else
{
lean_object* v_tk_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_tk_971_ = l_Lean_Syntax_getArg(v___x_949_, v___x_591_);
v___x_972_ = l_Lean_Syntax_getArg(v___x_949_, v___x_807_);
v___x_973_ = l_Lean_Syntax_getArg(v___x_949_, v___y_937_);
v___x_974_ = l_Lean_Syntax_isNone(v___x_973_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; 
lean_inc(v___x_973_);
v___x_975_ = l_Lean_Syntax_matchesNull(v___x_973_, v___y_937_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec(v___x_973_);
lean_dec(v___x_972_);
lean_dec(v_tk_971_);
lean_dec(v___x_949_);
lean_del_object(v___x_943_);
v___x_976_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5));
lean_inc_ref(v___y_933_);
v___x_977_ = l_Lean_Macro_throwErrorAt___redArg(v_val_941_, v___x_976_, v___y_933_, v___y_936_);
lean_dec(v_val_941_);
v___y_924_ = v___y_934_;
v___y_925_ = v_opts_x3f_939_;
v___y_926_ = v___x_940_;
v___y_927_ = v___y_933_;
v___y_928_ = v___y_937_;
v___y_929_ = v___x_977_;
goto v___jp_923_;
}
else
{
lean_object* v_rev_x3f_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_rev_x3f_978_ = l_Lean_Syntax_getArg(v___x_973_, v___x_807_);
lean_dec(v___x_973_);
v___x_979_ = lean_box(0);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_rev_x3f_978_);
v___x_981_ = v___x_943_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_rev_x3f_978_);
v___x_981_ = v_reuseFailAlloc_983_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; 
lean_inc_ref(v___y_933_);
v___x_982_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_586_, v___x_972_, v_tk_971_, v___x_949_, v___y_935_, v___y_937_, v_val_941_, v___x_807_, v___x_979_, v___x_981_, v___y_933_, v___y_936_);
lean_dec(v_val_941_);
lean_dec(v___x_949_);
lean_dec(v_tk_971_);
v___y_924_ = v___y_934_;
v___y_925_ = v_opts_x3f_939_;
v___y_926_ = v___x_940_;
v___y_927_ = v___y_933_;
v___y_928_ = v___y_937_;
v___y_929_ = v___x_982_;
goto v___jp_923_;
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v___x_973_);
lean_del_object(v___x_943_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_box(0);
lean_inc_ref(v___y_933_);
v___x_986_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_586_, v___x_972_, v_tk_971_, v___x_949_, v___y_935_, v___y_937_, v_val_941_, v___x_807_, v___x_984_, v___x_985_, v___y_933_, v___y_936_);
lean_dec(v_val_941_);
lean_dec(v___x_949_);
lean_dec(v_tk_971_);
v___y_924_ = v___y_934_;
v___y_925_ = v_opts_x3f_939_;
v___y_926_ = v___x_940_;
v___y_927_ = v___y_933_;
v___y_928_ = v___y_937_;
v___y_929_ = v___x_986_;
goto v___jp_923_;
}
}
}
}
}
}
v___jp_988_:
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_unsigned_to_nat(3u);
v___x_995_ = l_Lean_Syntax_getArg(v_stx_527_, v___x_994_);
v___x_996_ = l_Lean_Syntax_isNone(v___x_995_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
lean_inc(v___x_995_);
v___x_997_ = l_Lean_Syntax_matchesNull(v___x_995_, v___x_807_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v___x_995_);
lean_dec(v_src_x3f_993_);
lean_dec(v___y_989_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_998_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_999_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_998_, v___y_990_, v___y_991_);
lean_dec(v_stx_527_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = l_Lean_Syntax_getArg(v___x_995_, v___x_591_);
lean_dec(v___x_995_);
v___x_1001_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117));
lean_inc(v___x_1000_);
v___x_1002_ = l_Lean_Syntax_isOfKind(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v___x_1000_);
lean_dec(v_src_x3f_993_);
lean_dec(v___y_989_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_1003_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_1004_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_1003_, v___y_990_, v___y_991_);
lean_dec(v_stx_527_);
return v___x_1004_;
}
else
{
lean_object* v_opts_x3f_1005_; lean_object* v___x_1006_; 
lean_dec(v_stx_527_);
v_opts_x3f_1005_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_807_);
lean_dec(v___x_1000_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_opts_x3f_1005_);
v___y_933_ = v___y_990_;
v___y_934_ = v___y_989_;
v___y_935_ = v___x_994_;
v___y_936_ = v___y_991_;
v___y_937_ = v___y_992_;
v___y_938_ = v_src_x3f_993_;
v_opts_x3f_939_ = v___x_1006_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v___x_1007_; 
lean_dec(v___x_995_);
lean_dec(v_stx_527_);
v___x_1007_ = lean_box(0);
v___y_933_ = v___y_990_;
v___y_934_ = v___y_989_;
v___y_935_ = v___x_994_;
v___y_936_ = v___y_991_;
v___y_937_ = v___y_992_;
v___y_938_ = v_src_x3f_993_;
v_opts_x3f_939_ = v___x_1007_;
goto v___jp_932_;
}
}
v___jp_1008_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = lean_unsigned_to_nat(2u);
v___x_1013_ = l_Lean_Syntax_getArg(v_stx_527_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_isNone(v___x_1013_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; 
lean_inc(v___x_1013_);
v___x_1015_ = l_Lean_Syntax_matchesNull(v___x_1013_, v___x_807_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_1013_);
lean_dec(v_ver_x3f_1009_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_1016_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_1017_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_1016_, v___y_1010_, v___y_1011_);
lean_dec(v_stx_527_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = l_Lean_Syntax_getArg(v___x_1013_, v___x_591_);
lean_dec(v___x_1013_);
v___x_1019_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119));
lean_inc(v___x_1018_);
v___x_1020_ = l_Lean_Syntax_isOfKind(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v___x_1018_);
lean_dec(v_ver_x3f_1009_);
lean_dec(v___x_806_);
lean_dec(v_doc_x3f_528_);
v___x_1021_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_1022_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_527_, v___x_1021_, v___y_1010_, v___y_1011_);
lean_dec(v_stx_527_);
return v___x_1022_;
}
else
{
lean_object* v_src_x3f_1023_; lean_object* v___x_1024_; 
v_src_x3f_1023_ = l_Lean_Syntax_getArg(v___x_1018_, v___x_807_);
lean_dec(v___x_1018_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_src_x3f_1023_);
v___y_989_ = v_ver_x3f_1009_;
v___y_990_ = v___y_1010_;
v___y_991_ = v___y_1011_;
v___y_992_ = v___x_1012_;
v_src_x3f_993_ = v___x_1024_;
goto v___jp_988_;
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v___x_1013_);
v___x_1025_ = lean_box(0);
v___y_989_ = v_ver_x3f_1009_;
v___y_990_ = v___y_1010_;
v___y_991_ = v___y_1011_;
v___y_992_ = v___x_1012_;
v_src_x3f_993_ = v___x_1025_;
goto v___jp_988_;
}
}
}
v___jp_531_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc(v___y_535_);
lean_inc(v___y_541_);
lean_inc(v___y_548_);
v___x_560_ = l_Lean_Syntax_node3(v___y_548_, v___y_557_, v___y_541_, v___y_535_, v___y_559_);
lean_inc_n(v___y_535_, 2);
lean_inc(v___y_556_);
lean_inc(v___y_548_);
v___x_561_ = l_Lean_Syntax_node3(v___y_548_, v___y_556_, v___y_535_, v___y_535_, v___x_560_);
lean_inc(v___y_548_);
v___x_562_ = l_Lean_Syntax_node2(v___y_548_, v___y_547_, v___y_540_, v___x_561_);
v___x_563_ = lean_unsigned_to_nat(10u);
v___x_564_ = lean_mk_empty_array_with_capacity(v___x_563_);
v___x_565_ = lean_array_push(v___x_564_, v___y_539_);
lean_inc(v___y_534_);
v___x_566_ = lean_array_push(v___x_565_, v___y_534_);
v___x_567_ = lean_array_push(v___x_566_, v___y_554_);
lean_inc(v___y_534_);
v___x_568_ = lean_array_push(v___x_567_, v___y_534_);
v___x_569_ = lean_array_push(v___x_568_, v___y_532_);
lean_inc(v___y_534_);
v___x_570_ = lean_array_push(v___x_569_, v___y_534_);
v___x_571_ = lean_array_push(v___x_570_, v___y_538_);
lean_inc(v___y_534_);
v___x_572_ = lean_array_push(v___x_571_, v___y_534_);
v___x_573_ = lean_array_push(v___x_572_, v___x_562_);
v___x_574_ = lean_array_push(v___x_573_, v___y_534_);
lean_inc(v___y_548_);
v___x_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_575_, 0, v___y_548_);
lean_ctor_set(v___x_575_, 1, v___y_556_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
lean_inc(v___y_548_);
v___x_576_ = l_Lean_Syntax_node1(v___y_548_, v___y_543_, v___x_575_);
lean_inc_n(v___y_535_, 2);
lean_inc(v___y_548_);
v___x_577_ = l_Lean_Syntax_node6(v___y_548_, v___y_550_, v___y_555_, v___y_535_, v___x_576_, v___y_536_, v___y_535_, v___y_545_);
v___x_578_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0));
v___x_579_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1));
v___x_580_ = l_Lean_Name_mkStr4(v___y_533_, v___y_552_, v___x_578_, v___x_579_);
lean_inc_n(v___y_535_, 2);
lean_inc(v___y_548_);
v___x_581_ = l_Lean_Syntax_node2(v___y_548_, v___x_580_, v___y_535_, v___y_535_);
lean_inc(v___y_535_);
lean_inc(v___y_548_);
v___x_582_ = l_Lean_Syntax_node4(v___y_548_, v___y_553_, v___y_541_, v___x_577_, v___x_581_, v___y_535_);
lean_inc(v___y_548_);
v___x_583_ = l_Lean_Syntax_node5(v___y_548_, v___y_551_, v___y_542_, v___y_537_, v___y_558_, v___x_582_, v___y_535_);
v___x_584_ = l_Lean_Syntax_node2(v___y_548_, v___y_546_, v___y_549_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___y_544_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(lean_object* v_stx_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
lean_inc(v_stx_1045_);
v___x_1049_ = l_Lean_Syntax_isOfKind(v_stx_1045_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2));
v___x_1051_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1045_, v___x_1050_, v_a_1046_, v_a_1047_);
lean_dec(v_stx_1045_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_kw_1055_; lean_object* v___x_1056_; lean_object* v_spec_1057_; lean_object* v___y_1059_; lean_object* v___x_1093_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Lean_Syntax_getArg(v_stx_1045_, v___x_1052_);
v___x_1054_ = lean_unsigned_to_nat(1u);
v_kw_1055_ = l_Lean_Syntax_getArg(v_stx_1045_, v___x_1054_);
v___x_1056_ = lean_unsigned_to_nat(2u);
v_spec_1057_ = l_Lean_Syntax_getArg(v_stx_1045_, v___x_1056_);
lean_dec(v_stx_1045_);
v___x_1093_ = l_Lean_Syntax_getOptional_x3f(v___x_1053_);
lean_dec(v___x_1053_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
v___y_1059_ = v___x_1094_;
goto v___jp_1058_;
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_val_1095_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1093_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_val_1095_);
lean_dec(v___x_1093_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_val_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v___y_1059_ = v___x_1100_;
goto v___jp_1058_;
}
}
}
v___jp_1058_:
{
lean_object* v_methods_1060_; lean_object* v_quotContext_1061_; lean_object* v_currMacroScope_1062_; lean_object* v_currRecDepth_1063_; lean_object* v_maxRecDepth_1064_; lean_object* v_ref_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1092_; 
v_methods_1060_ = lean_ctor_get(v_a_1046_, 0);
v_quotContext_1061_ = lean_ctor_get(v_a_1046_, 1);
v_currMacroScope_1062_ = lean_ctor_get(v_a_1046_, 2);
v_currRecDepth_1063_ = lean_ctor_get(v_a_1046_, 3);
v_maxRecDepth_1064_ = lean_ctor_get(v_a_1046_, 4);
v_ref_1065_ = lean_ctor_get(v_a_1046_, 5);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1046_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1067_ = v_a_1046_;
v_isShared_1068_ = v_isSharedCheck_1092_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_ref_1065_);
lean_inc(v_maxRecDepth_1064_);
lean_inc(v_currRecDepth_1063_);
lean_inc(v_currMacroScope_1062_);
lean_inc(v_quotContext_1061_);
lean_inc(v_methods_1060_);
lean_dec(v_a_1046_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1092_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_ref_1069_; lean_object* v___x_1071_; 
v_ref_1069_ = l_Lean_replaceRef(v_kw_1055_, v_ref_1065_);
lean_dec(v_ref_1065_);
lean_dec(v_kw_1055_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 5, v_ref_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_methods_1060_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_quotContext_1061_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_currMacroScope_1062_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_currRecDepth_1063_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_maxRecDepth_1064_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_ref_1069_);
v___x_1071_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(v_spec_1057_, v___y_1059_, v___x_1071_, v_a_1047_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_a_1074_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1082_ = lean_ctor_get(v___x_1072_, 0);
v_a_1083_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1072_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_inc(v_a_1082_);
lean_dec(v___x_1072_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1(){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = l_Lean_Elab_macroAttribute;
v___x_1132_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
v___x_1133_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10));
v___x_1134_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl), 3, 0);
v___x_1135_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1131_, v___x_1132_, v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___boxed(lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
return v_res_1137_;
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
