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
lean_object* l_Array_mkArray0___redArg();
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
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DependencySrc.path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DependencySrc"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 123, 123, 148, 32, 75, 229, 138)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 247, 255, 238, 70, 62, 187, 2)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__9 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "DependencySrc.git"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 123, 123, 148, 32, 75, 229, 138)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 37, 72, 153, 12, 75, 97, 98)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed from syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
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
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "InputVer.git"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "InputVer"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(66, 43, 100, 232, 179, 14, 35, 233)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 242, 10, 14, 134, 113, 46, 22)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 200, 168, 53, 212, 85, 80, 128)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verSpec"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value),LEAN_SCALAR_PTR_LITERAL(5, 204, 227, 250, 63, 151, 124, 47)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ill-formed version syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value_aux_2),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalVer"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value),LEAN_SCALAR_PTR_LITERAL(15, 252, 213, 234, 103, 11, 172, 191)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eval_ver%"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(66, 43, 100, 232, 179, 14, 35, 233)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromSource"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 246, 101, 8, 76, 68, 147)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "InputVer.none"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value;
static lean_once_cell_t l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(66, 43, 100, 232, 179, 14, 35, 233)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 64, 189, 110, 204, 212, 206, 149)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 190, 59, 35, 131, 146, 80, 44)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fromGit"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value),LEAN_SCALAR_PTR_LITERAL(58, 198, 35, 138, 239, 183, 90, 121)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed name syntax"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__126 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__126_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depName"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__127 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__127_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__127_value),LEAN_SCALAR_PTR_LITERAL(11, 76, 0, 7, 47, 106, 167, 185)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromPath"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__129 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__129_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__129_value),LEAN_SCALAR_PTR_LITERAL(88, 231, 238, 12, 211, 124, 7, 152)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "withClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__131 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__131_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__131_value),LEAN_SCALAR_PTR_LITERAL(62, 242, 50, 31, 135, 230, 200, 221)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__133 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__133_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__133_value),LEAN_SCALAR_PTR_LITERAL(108, 123, 128, 15, 141, 170, 246, 11)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134_value;
static const lean_string_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "verClause"};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__135 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__135_value;
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value_aux_0),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value_aux_1),((lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__135_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 66, 152, 98, 148, 165, 231)}};
static const lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136 = (const lean_object*)&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136_value;
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
lean_inc_n(v_info_37_, 2);
v___x_46_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_46_, 0, v_info_37_);
lean_ctor_set(v___x_46_, 1, v___x_42_);
lean_ctor_set(v___x_46_, 2, v___x_44_);
lean_ctor_set(v___x_46_, 3, v___x_45_);
v___x_47_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
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
lean_inc_n(v_toBind_123_, 4);
lean_dec_ref(v_inst_116_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc_n(v_toPure_124_, 2);
lean_dec_ref(v_toApplicative_119_);
v_val_125_ = lean_ctor_get(v_term_x3f_118_, 0);
lean_inc_n(v_val_125_, 2);
lean_dec_ref_known(v_term_x3f_118_, 1);
v_getRef_126_ = lean_ctor_get(v_toMonadRef_120_, 0);
lean_inc_n(v_getRef_126_, 2);
v_withRef_127_ = lean_ctor_get(v_toMonadRef_120_, 1);
lean_inc(v_withRef_127_);
lean_dec_ref(v_toMonadRef_120_);
v___f_128_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_128_, 0, v_toPure_124_);
v___f_129_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 6, 5);
lean_closure_set(v___f_129_, 0, v_val_125_);
lean_closure_set(v___f_129_, 1, v_toPure_124_);
lean_closure_set(v___f_129_, 2, v_toBind_123_);
lean_closure_set(v___f_129_, 3, v_getContext_122_);
lean_closure_set(v___f_129_, 4, v_getCurrMacroScope_121_);
v___x_130_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v_getRef_126_, v___f_128_);
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
lean_inc_n(v_toBind_137_, 3);
lean_dec_ref(v_inst_116_);
v_toPure_138_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc_n(v_toPure_138_, 2);
lean_dec_ref(v_toApplicative_119_);
v_getRef_139_ = lean_ctor_get(v_toMonadRef_134_, 0);
lean_inc(v_getRef_139_);
lean_dec_ref(v_toMonadRef_134_);
v___f_140_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_140_, 0, v_toPure_138_);
v___f_141_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7), 5, 4);
lean_closure_set(v___f_141_, 0, v_toPure_138_);
lean_closure_set(v___f_141_, 1, v_toBind_137_);
lean_closure_set(v___f_141_, 2, v_getContext_136_);
lean_closure_set(v___f_141_, 3, v_getCurrMacroScope_135_);
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
lean_inc_n(v_toBind_152_, 4);
lean_dec_ref(v_inst_145_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc_n(v_toPure_153_, 2);
lean_dec_ref(v_toApplicative_148_);
v_val_154_ = lean_ctor_get(v_term_x3f_147_, 0);
lean_inc_n(v_val_154_, 2);
lean_dec_ref_known(v_term_x3f_147_, 1);
v_getRef_155_ = lean_ctor_get(v_toMonadRef_149_, 0);
lean_inc_n(v_getRef_155_, 2);
v_withRef_156_ = lean_ctor_get(v_toMonadRef_149_, 1);
lean_inc(v_withRef_156_);
lean_dec_ref(v_toMonadRef_149_);
v___f_157_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_157_, 0, v_toPure_153_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3), 6, 5);
lean_closure_set(v___f_158_, 0, v_val_154_);
lean_closure_set(v___f_158_, 1, v_toPure_153_);
lean_closure_set(v___f_158_, 2, v_toBind_152_);
lean_closure_set(v___f_158_, 3, v_getContext_151_);
lean_closure_set(v___f_158_, 4, v_getCurrMacroScope_150_);
v___x_159_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v_getRef_155_, v___f_157_);
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
lean_inc_n(v_toBind_166_, 3);
lean_dec_ref(v_inst_145_);
v_toPure_167_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc_n(v_toPure_167_, 2);
lean_dec_ref(v_toApplicative_148_);
v_getRef_168_ = lean_ctor_get(v_toMonadRef_163_, 0);
lean_inc(v_getRef_168_);
lean_dec_ref(v_toMonadRef_163_);
v___f_169_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v_toPure_167_);
v___f_170_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7), 5, 4);
lean_closure_set(v___f_170_, 0, v_toPure_167_);
lean_closure_set(v___f_170_, 1, v_toBind_166_);
lean_closure_set(v___f_170_, 2, v_getContext_165_);
lean_closure_set(v___f_170_, 3, v_getCurrMacroScope_164_);
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
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__7));
v___x_187_ = l_Lean_mkCIdent(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__10));
v___x_193_ = l_Lean_mkCIdent(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(lean_object* v___x_194_, lean_object* v___x_195_, lean_object* v_val_196_, uint8_t v___x_197_, lean_object* v___x_198_, lean_object* v_x_199_, lean_object* v_copyTk_x3f_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_quotContext_203_; lean_object* v_currMacroScope_204_; lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v_ref_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___y_224_; 
v_quotContext_203_ = lean_ctor_get(v___y_201_, 1);
v_currMacroScope_204_ = lean_ctor_get(v___y_201_, 2);
v_ref_205_ = lean_ctor_get(v___y_201_, 5);
v___x_206_ = l_Lean_Syntax_getArg(v___x_194_, v___x_195_);
v_ref_207_ = l_Lean_replaceRef(v_val_196_, v_ref_205_);
v___x_208_ = l_Lean_SourceInfo_fromRef(v_ref_207_, v___x_197_);
lean_dec(v_ref_207_);
v___x_209_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_210_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1);
v___x_211_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2));
v___x_212_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3));
v___x_213_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4));
lean_inc(v_currMacroScope_204_);
lean_inc(v_quotContext_203_);
v___x_214_ = l_Lean_addMacroScope(v_quotContext_203_, v___x_213_, v_currMacroScope_204_);
v___x_215_ = l_Lean_Name_mkStr3(v___x_198_, v___x_211_, v___x_212_);
v___x_216_ = lean_box(0);
lean_inc(v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_216_);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
lean_inc(v___x_208_);
v___x_221_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_221_, 0, v___x_208_);
lean_ctor_set(v___x_221_, 1, v___x_210_);
lean_ctor_set(v___x_221_, 2, v___x_214_);
lean_ctor_set(v___x_221_, 3, v___x_220_);
v___x_222_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
if (lean_obj_tag(v_copyTk_x3f_200_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__8);
v___y_224_ = v___x_228_;
goto v___jp_223_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__11);
v___y_224_ = v___x_229_;
goto v___jp_223_;
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_inc(v___y_224_);
lean_inc(v___x_208_);
v___x_225_ = l_Lean_Syntax_node2(v___x_208_, v___x_222_, v___x_206_, v___y_224_);
v___x_226_ = l_Lean_Syntax_node2(v___x_208_, v___x_209_, v___x_221_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___y_202_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___boxed(lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_val_232_, lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v_x_235_, lean_object* v_copyTk_x3f_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
uint8_t v___x_47235__boxed_239_; lean_object* v_res_240_; 
v___x_47235__boxed_239_ = lean_unbox(v___x_233_);
v_res_240_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_230_, v___x_231_, v_val_232_, v___x_47235__boxed_239_, v___x_234_, v_x_235_, v_copyTk_x3f_236_, v___y_237_, v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_copyTk_x3f_236_);
lean_dec(v_val_232_);
lean_dec(v___x_231_);
lean_dec(v___x_230_);
return v_res_240_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__0));
v___x_243_ = l_String_toRawSubstring_x27(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1(lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v_tk_251_, lean_object* v___x_252_, lean_object* v___x_253_, lean_object* v___x_254_, lean_object* v_val_255_, lean_object* v___x_256_, lean_object* v_x_257_, lean_object* v_rev_x3f_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v_a_292_; lean_object* v_a_293_; lean_object* v_subDir_x3f_315_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = l_Lean_Syntax_getArg(v___x_252_, v___x_253_);
v___x_341_ = l_Lean_Syntax_isNone(v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
lean_inc(v___x_340_);
v___x_342_ = l_Lean_Syntax_matchesNull(v___x_340_, v___x_254_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v___x_340_);
lean_dec(v_rev_x3f_258_);
lean_dec(v___x_250_);
lean_dec_ref(v___x_249_);
v___x_343_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4));
v___x_344_ = l_Lean_Macro_throwErrorAt___redArg(v_val_255_, v___x_343_, v___y_259_, v___y_260_);
return v___x_344_;
}
else
{
lean_object* v_subDir_x3f_345_; lean_object* v___x_346_; 
v_subDir_x3f_345_ = l_Lean_Syntax_getArg(v___x_340_, v___x_256_);
lean_dec(v___x_340_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_subDir_x3f_345_);
v_subDir_x3f_315_ = v___x_346_;
goto v___jp_314_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec(v___x_340_);
v___x_347_ = lean_box(0);
v_subDir_x3f_315_ = v___x_347_;
goto v___jp_314_;
}
v___jp_261_:
{
uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_268_ = 0;
v___x_269_ = l_Lean_SourceInfo_fromRef(v___y_263_, v___x_268_);
lean_dec(v___y_263_);
v___x_270_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_271_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__1);
v___x_272_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2));
v___x_273_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__2));
v___x_274_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__3));
v___x_275_ = l_Lean_addMacroScope(v___y_262_, v___x_274_, v___y_264_);
v___x_276_ = l_Lean_Name_mkStr3(v___x_249_, v___x_272_, v___x_273_);
v___x_277_ = lean_box(0);
lean_inc(v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_277_);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
lean_inc_n(v___x_269_, 2);
v___x_282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_282_, 0, v___x_269_);
lean_ctor_set(v___x_282_, 1, v___x_271_);
lean_ctor_set(v___x_282_, 2, v___x_275_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_284_ = l_Lean_Syntax_node3(v___x_269_, v___x_283_, v___x_250_, v___y_265_, v_a_266_);
v___x_285_ = l_Lean_Syntax_node2(v___x_269_, v___x_270_, v___x_282_, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_a_267_);
return v___x_286_;
}
v___jp_287_:
{
if (lean_obj_tag(v___y_290_) == 1)
{
lean_object* v_val_294_; lean_object* v_ref_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_val_294_ = lean_ctor_get(v___y_290_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___y_290_, 1);
v_ref_295_ = l_Lean_replaceRef(v_val_294_, v___y_289_);
v___x_296_ = 0;
v___x_297_ = l_Lean_SourceInfo_fromRef(v_ref_295_, v___x_296_);
lean_dec(v_ref_295_);
v___x_298_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_299_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_300_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v___y_291_);
lean_inc(v___y_288_);
v___x_301_ = l_Lean_addMacroScope(v___y_288_, v___x_300_, v___y_291_);
v___x_302_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc_n(v___x_297_, 2);
v___x_303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_303_, 0, v___x_297_);
lean_ctor_set(v___x_303_, 1, v___x_299_);
lean_ctor_set(v___x_303_, 2, v___x_301_);
lean_ctor_set(v___x_303_, 3, v___x_302_);
v___x_304_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_305_ = l_Lean_Syntax_node1(v___x_297_, v___x_304_, v_val_294_);
v___x_306_ = l_Lean_Syntax_node2(v___x_297_, v___x_298_, v___x_303_, v___x_305_);
v___y_262_ = v___y_288_;
v___y_263_ = v___y_289_;
v___y_264_ = v___y_291_;
v___y_265_ = v_a_292_;
v_a_266_ = v___x_306_;
v_a_267_ = v_a_293_;
goto v___jp_261_;
}
else
{
uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v___y_290_);
v___x_307_ = 0;
v___x_308_ = l_Lean_SourceInfo_fromRef(v___y_289_, v___x_307_);
v___x_309_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_310_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc(v___y_291_);
lean_inc(v___y_288_);
v___x_311_ = l_Lean_addMacroScope(v___y_288_, v___x_310_, v___y_291_);
v___x_312_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_313_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_313_, 0, v___x_308_);
lean_ctor_set(v___x_313_, 1, v___x_309_);
lean_ctor_set(v___x_313_, 2, v___x_311_);
lean_ctor_set(v___x_313_, 3, v___x_312_);
v___y_262_ = v___y_288_;
v___y_263_ = v___y_289_;
v___y_264_ = v___y_291_;
v___y_265_ = v_a_292_;
v_a_266_ = v___x_313_;
v_a_267_ = v_a_293_;
goto v___jp_261_;
}
}
v___jp_314_:
{
lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v_ref_318_; lean_object* v_ref_319_; 
v_quotContext_316_ = lean_ctor_get(v___y_259_, 1);
v_currMacroScope_317_ = lean_ctor_get(v___y_259_, 2);
v_ref_318_ = lean_ctor_get(v___y_259_, 5);
v_ref_319_ = l_Lean_replaceRef(v_tk_251_, v_ref_318_);
if (lean_obj_tag(v_rev_x3f_258_) == 1)
{
lean_object* v_val_320_; lean_object* v_ref_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_val_320_ = lean_ctor_get(v_rev_x3f_258_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v_rev_x3f_258_, 1);
v_ref_321_ = l_Lean_replaceRef(v_val_320_, v_ref_319_);
v___x_322_ = 0;
v___x_323_ = l_Lean_SourceInfo_fromRef(v_ref_321_, v___x_322_);
lean_dec(v_ref_321_);
v___x_324_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_325_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_326_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc_n(v_currMacroScope_317_, 2);
lean_inc_n(v_quotContext_316_, 2);
v___x_327_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_326_, v_currMacroScope_317_);
v___x_328_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc_n(v___x_323_, 2);
v___x_329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_329_, 0, v___x_323_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_327_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
v___x_330_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_331_ = l_Lean_Syntax_node1(v___x_323_, v___x_330_, v_val_320_);
v___x_332_ = l_Lean_Syntax_node2(v___x_323_, v___x_324_, v___x_329_, v___x_331_);
v___y_288_ = v_quotContext_316_;
v___y_289_ = v_ref_319_;
v___y_290_ = v_subDir_x3f_315_;
v___y_291_ = v_currMacroScope_317_;
v_a_292_ = v___x_332_;
v_a_293_ = v___y_260_;
goto v___jp_287_;
}
else
{
uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_rev_x3f_258_);
v___x_333_ = 0;
v___x_334_ = l_Lean_SourceInfo_fromRef(v_ref_319_, v___x_333_);
v___x_335_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_336_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc_n(v_currMacroScope_317_, 2);
lean_inc_n(v_quotContext_316_, 2);
v___x_337_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_336_, v_currMacroScope_317_);
v___x_338_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_339_, 0, v___x_334_);
lean_ctor_set(v___x_339_, 1, v___x_335_);
lean_ctor_set(v___x_339_, 2, v___x_337_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
v___y_288_ = v_quotContext_316_;
v___y_289_ = v_ref_319_;
v___y_290_ = v_subDir_x3f_315_;
v___y_291_ = v_currMacroScope_317_;
v_a_292_ = v___x_339_;
v_a_293_ = v___y_260_;
goto v___jp_287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___boxed(lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_tk_350_, lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v___x_353_, lean_object* v_val_354_, lean_object* v___x_355_, lean_object* v_x_356_, lean_object* v_rev_x3f_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1(v___x_348_, v___x_349_, v_tk_350_, v___x_351_, v___x_352_, v___x_353_, v_val_354_, v___x_355_, v_x_356_, v_rev_x3f_357_, v___y_358_, v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_355_);
lean_dec(v_val_354_);
lean_dec(v___x_353_);
lean_dec(v___x_352_);
lean_dec(v___x_351_);
lean_dec(v_tk_350_);
return v_res_360_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3));
v___x_366_ = l_String_toRawSubstring_x27(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_371_ = l_String_toRawSubstring_x27(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9));
v___x_376_ = l_String_toRawSubstring_x27(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12));
v___x_381_ = l_String_toRawSubstring_x27(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26));
v___x_400_ = l_String_toRawSubstring_x27(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38));
v___x_417_ = l_Lean_mkCIdent(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44));
v___x_424_ = l_String_toRawSubstring_x27(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Array_mkArray0___redArg();
return v___x_445_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70));
v___x_475_ = l_String_toRawSubstring_x27(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89));
v___x_519_ = l_String_toRawSubstring_x27(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72));
v___x_559_ = l_String_toRawSubstring_x27(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116));
v___x_584_ = l_String_toRawSubstring_x27(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(lean_object* v_stx_634_, lean_object* v_doc_x3f_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15));
v___x_773_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18));
lean_inc(v_stx_634_);
v___x_774_ = l_Lean_Syntax_isOfKind(v_stx_634_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_doc_x3f_635_);
v___x_775_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_776_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_775_, v_a_636_, v_a_637_);
lean_dec(v_stx_634_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v_quotContext_891_; lean_object* v_currMacroScope_892_; lean_object* v_ref_893_; lean_object* v___y_894_; lean_object* v_a_895_; lean_object* v_a_896_; lean_object* v_val_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v_ver_931_; lean_object* v_quotContext_932_; lean_object* v_currMacroScope_933_; lean_object* v_ref_934_; lean_object* v___y_935_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_ver_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_a_1142_; lean_object* v_a_1143_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v_opts_x3f_1177_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v_src_x3f_1230_; lean_object* v_ver_x3f_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = l_Lean_Syntax_getArg(v_stx_634_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_1263_ = l_Lean_Syntax_getArg(v_stx_634_, v___x_779_);
v___x_1264_ = l_Lean_Syntax_isNone(v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; 
lean_inc(v___x_1263_);
v___x_1265_ = l_Lean_Syntax_matchesNull(v___x_1263_, v___x_779_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v___x_1263_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1266_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1267_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1266_, v_a_636_, v_a_637_);
lean_dec(v_stx_634_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_777_);
lean_dec(v___x_1263_);
v___x_1269_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__136));
lean_inc(v___x_1268_);
v___x_1270_ = l_Lean_Syntax_isOfKind(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v___x_1268_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1271_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1272_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1271_, v_a_636_, v_a_637_);
lean_dec(v_stx_634_);
return v___x_1272_;
}
else
{
lean_object* v_ver_x3f_1273_; lean_object* v___x_1274_; 
v_ver_x3f_1273_ = l_Lean_Syntax_getArg(v___x_1268_, v___x_779_);
lean_dec(v___x_1268_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_ver_x3f_1273_);
v_ver_x3f_1246_ = v___x_1274_;
v___y_1247_ = v_a_636_;
v___y_1248_ = v_a_637_;
goto v___jp_1245_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v___x_1263_);
v___x_1275_ = lean_box(0);
v_ver_x3f_1246_ = v___x_1275_;
v___y_1247_ = v_a_636_;
v___y_1248_ = v_a_637_;
goto v___jp_1245_;
}
v___jp_780_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_inc_ref(v___y_785_);
v___x_807_ = l_Array_append___redArg(v___y_785_, v___y_806_);
lean_dec_ref(v___y_806_);
lean_inc_n(v___y_796_, 5);
lean_inc_n(v___y_799_, 19);
v___x_808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_808_, 0, v___y_799_);
lean_ctor_set(v___x_808_, 1, v___y_796_);
lean_ctor_set(v___x_808_, 2, v___x_807_);
v___x_809_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20));
lean_inc_ref_n(v___y_802_, 7);
lean_inc_ref_n(v___y_788_, 12);
lean_inc_ref_n(v___y_783_, 12);
v___x_810_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21));
v___x_812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_812_, 0, v___y_799_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22));
v___x_814_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23));
v___x_816_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_815_);
lean_inc_n(v___y_794_, 9);
v___x_817_ = l_Lean_Syntax_node1(v___y_799_, v___x_816_, v___y_794_);
v___x_818_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24));
v___x_819_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25));
v___x_820_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___x_818_, v___x_819_);
v___x_821_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27);
v___x_822_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28));
lean_inc_n(v___y_792_, 2);
lean_inc_n(v___y_803_, 2);
v___x_823_ = l_Lean_addMacroScope(v___y_803_, v___x_822_, v___y_792_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_825_, 0, v___y_799_);
lean_ctor_set(v___x_825_, 1, v___x_821_);
lean_ctor_set(v___x_825_, 2, v___x_823_);
lean_ctor_set(v___x_825_, 3, v___x_824_);
v___x_826_ = l_Lean_Syntax_node2(v___y_799_, v___x_820_, v___x_825_, v___y_794_);
v___x_827_ = l_Lean_Syntax_node2(v___y_799_, v___x_814_, v___x_817_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node1(v___y_799_, v___y_796_, v___x_827_);
v___x_829_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_799_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_Syntax_node3(v___y_799_, v___x_810_, v___x_812_, v___x_828_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node1(v___y_799_, v___y_796_, v___x_831_);
lean_inc(v___y_805_);
v___x_833_ = l_Lean_Syntax_node7(v___y_799_, v___y_805_, v___x_808_, v___x_832_, v___y_794_, v___y_794_, v___y_794_, v___y_794_, v___y_794_);
v___x_834_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30));
lean_inc_ref_n(v___y_790_, 4);
v___x_835_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_790_, v___x_834_);
v___x_836_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31));
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_799_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32));
v___x_839_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_790_, v___x_838_);
v___x_840_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33));
v___x_841_ = lean_box(2);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___y_796_);
lean_ctor_set(v___x_842_, 2, v___x_840_);
v___x_843_ = lean_mk_empty_array_with_capacity(v___y_801_);
lean_inc(v___y_804_);
v___x_844_ = lean_array_push(v___x_843_, v___y_804_);
v___x_845_ = lean_array_push(v___x_844_, v___x_842_);
v___x_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_846_, 0, v___x_841_);
lean_ctor_set(v___x_846_, 1, v___x_839_);
lean_ctor_set(v___x_846_, 2, v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34));
v___x_848_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_790_, v___x_847_);
v___x_849_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35));
v___x_850_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_849_);
v___x_851_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36));
v___x_852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_852_, 0, v___y_799_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39);
v___x_854_ = l_Lean_Syntax_node2(v___y_799_, v___x_850_, v___x_852_, v___x_853_);
v___x_855_ = l_Lean_Syntax_node1(v___y_799_, v___y_796_, v___x_854_);
v___x_856_ = l_Lean_Syntax_node2(v___y_799_, v___x_848_, v___y_794_, v___x_855_);
v___x_857_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40));
v___x_858_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_790_, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_799_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42));
v___x_862_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_861_);
v___x_863_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43));
v___x_864_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_863_);
v___x_865_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45);
v___x_866_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46));
v___x_867_ = l_Lean_addMacroScope(v___y_803_, v___x_866_, v___y_792_);
v___x_868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_868_, 0, v___y_799_);
lean_ctor_set(v___x_868_, 1, v___x_865_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
lean_ctor_set(v___x_868_, 3, v___x_824_);
lean_inc(v___x_864_);
v___x_869_ = l_Lean_Syntax_node2(v___y_799_, v___x_864_, v___x_868_, v___y_794_);
v___x_870_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47));
v___x_871_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_870_);
v___x_872_ = l_Lean_TSyntax_getId(v___y_804_);
lean_dec(v___y_804_);
lean_inc(v___x_872_);
v___x_873_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_824_, v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_quoteNameMk(v___x_872_);
v___y_694_ = v___x_869_;
v___y_695_ = v___y_781_;
v___y_696_ = v___y_782_;
v___y_697_ = v___y_783_;
v___y_698_ = v___y_784_;
v___y_699_ = v___x_856_;
v___y_700_ = v___y_786_;
v___y_701_ = v___x_833_;
v___y_702_ = v___x_846_;
v___y_703_ = v___y_787_;
v___y_704_ = v___y_788_;
v___y_705_ = v___x_862_;
v___y_706_ = v___x_860_;
v___y_707_ = v___y_789_;
v___y_708_ = v___y_790_;
v___y_709_ = v___y_791_;
v___y_710_ = v___y_793_;
v___y_711_ = v___y_792_;
v___y_712_ = v___y_794_;
v___y_713_ = v___x_835_;
v___y_714_ = v___x_864_;
v___y_715_ = v___y_795_;
v___y_716_ = v___x_858_;
v___y_717_ = v___y_797_;
v___y_718_ = v___y_796_;
v___y_719_ = v___y_798_;
v___y_720_ = v___y_800_;
v___y_721_ = v___y_799_;
v___y_722_ = v___x_871_;
v___y_723_ = v___y_803_;
v___y_724_ = v___x_837_;
v___y_725_ = v___x_824_;
v___y_726_ = v___x_874_;
goto v___jp_693_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v___x_872_);
v_val_875_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_873_, 1);
v___x_876_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48));
lean_inc_ref(v___y_802_);
lean_inc_ref(v___y_788_);
lean_inc_ref(v___y_783_);
v___x_877_ = l_Lean_Name_mkStr4(v___y_783_, v___y_788_, v___y_802_, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49));
v___x_879_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50));
v___x_880_ = lean_string_intercalate(v___x_879_, v_val_875_);
v___x_881_ = lean_string_append(v___x_878_, v___x_880_);
lean_dec_ref(v___x_880_);
v___x_882_ = l_Lean_Syntax_mkNameLit(v___x_881_, v___x_841_);
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_884_ = lean_array_push(v___x_883_, v___x_882_);
v___x_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_885_, 0, v___x_841_);
lean_ctor_set(v___x_885_, 1, v___x_877_);
lean_ctor_set(v___x_885_, 2, v___x_884_);
v___y_694_ = v___x_869_;
v___y_695_ = v___y_781_;
v___y_696_ = v___y_782_;
v___y_697_ = v___y_783_;
v___y_698_ = v___y_784_;
v___y_699_ = v___x_856_;
v___y_700_ = v___y_786_;
v___y_701_ = v___x_833_;
v___y_702_ = v___x_846_;
v___y_703_ = v___y_787_;
v___y_704_ = v___y_788_;
v___y_705_ = v___x_862_;
v___y_706_ = v___x_860_;
v___y_707_ = v___y_789_;
v___y_708_ = v___y_790_;
v___y_709_ = v___y_791_;
v___y_710_ = v___y_793_;
v___y_711_ = v___y_792_;
v___y_712_ = v___y_794_;
v___y_713_ = v___x_835_;
v___y_714_ = v___x_864_;
v___y_715_ = v___y_795_;
v___y_716_ = v___x_858_;
v___y_717_ = v___y_797_;
v___y_718_ = v___y_796_;
v___y_719_ = v___y_798_;
v___y_720_ = v___y_800_;
v___y_721_ = v___y_799_;
v___y_722_ = v___x_871_;
v___y_723_ = v___y_803_;
v___y_724_ = v___x_837_;
v___y_725_ = v___x_824_;
v___y_726_ = v___x_885_;
goto v___jp_693_;
}
}
v___jp_886_:
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_897_ = 0;
v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_893_, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52));
v___x_900_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54));
v___x_901_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55));
lean_inc_n(v___x_898_, 8);
v___x_902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56));
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_898_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
lean_inc_ref_n(v___x_904_, 2);
lean_inc_ref_n(v___x_902_, 2);
v___x_905_ = l_Lean_Syntax_node2(v___x_898_, v___x_900_, v___x_902_, v___x_904_);
v___x_906_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0));
v___x_907_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1));
v___x_908_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2));
v___x_909_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58));
v___x_910_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_911_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59);
v___x_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_912_, 0, v___x_898_);
lean_ctor_set(v___x_912_, 1, v___x_910_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
v___x_913_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61));
lean_inc_ref_n(v___x_912_, 4);
v___x_914_ = l_Lean_Syntax_node1(v___x_898_, v___x_913_, v___x_912_);
v___x_915_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63));
v___x_916_ = l_Lean_Syntax_node1(v___x_898_, v___x_915_, v___x_912_);
lean_inc(v___x_916_);
v___x_917_ = l_Lean_Syntax_node6(v___x_898_, v___x_909_, v___x_902_, v___x_912_, v___x_914_, v___x_916_, v___x_912_, v___x_904_);
v___x_918_ = l_Lean_Syntax_node2(v___x_898_, v___x_899_, v___x_905_, v___x_917_);
v___x_919_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64));
v___x_920_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66));
v___x_921_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68));
if (lean_obj_tag(v_doc_x3f_635_) == 1)
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v_doc_x3f_635_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_doc_x3f_635_, 1);
v___x_923_ = l_Array_mkArray1___redArg(v_val_922_);
v___y_781_ = v___y_889_;
v___y_782_ = v_a_896_;
v___y_783_ = v___x_906_;
v___y_784_ = v___x_904_;
v___y_785_ = v___x_911_;
v___y_786_ = v___x_916_;
v___y_787_ = v___x_902_;
v___y_788_ = v___x_907_;
v___y_789_ = v___x_920_;
v___y_790_ = v___x_919_;
v___y_791_ = v_a_895_;
v___y_792_ = v_currMacroScope_892_;
v___y_793_ = v___x_918_;
v___y_794_ = v___x_912_;
v___y_795_ = v___x_913_;
v___y_796_ = v___x_910_;
v___y_797_ = v___y_888_;
v___y_798_ = v___y_887_;
v___y_799_ = v___x_898_;
v___y_800_ = v___x_909_;
v___y_801_ = v___y_890_;
v___y_802_ = v___x_908_;
v___y_803_ = v_quotContext_891_;
v___y_804_ = v___y_894_;
v___y_805_ = v___x_921_;
v___y_806_ = v___x_923_;
goto v___jp_780_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v_doc_x3f_635_);
v___x_924_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69));
v___y_781_ = v___y_889_;
v___y_782_ = v_a_896_;
v___y_783_ = v___x_906_;
v___y_784_ = v___x_904_;
v___y_785_ = v___x_911_;
v___y_786_ = v___x_916_;
v___y_787_ = v___x_902_;
v___y_788_ = v___x_907_;
v___y_789_ = v___x_920_;
v___y_790_ = v___x_919_;
v___y_791_ = v_a_895_;
v___y_792_ = v_currMacroScope_892_;
v___y_793_ = v___x_918_;
v___y_794_ = v___x_912_;
v___y_795_ = v___x_913_;
v___y_796_ = v___x_910_;
v___y_797_ = v___y_888_;
v___y_798_ = v___y_887_;
v___y_799_ = v___x_898_;
v___y_800_ = v___x_909_;
v___y_801_ = v___y_890_;
v___y_802_ = v___x_908_;
v___y_803_ = v_quotContext_891_;
v___y_804_ = v___y_894_;
v___y_805_ = v___x_921_;
v___y_806_ = v___x_924_;
goto v___jp_780_;
}
}
v___jp_925_:
{
lean_object* v___x_936_; lean_object* v_ref_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_936_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_930_);
v_ref_937_ = l_Lean_replaceRef(v_val_926_, v_ref_934_);
v___x_938_ = 0;
v___x_939_ = l_Lean_SourceInfo_fromRef(v_ref_937_, v___x_938_);
lean_dec(v_ref_937_);
v___x_940_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_941_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
v___x_942_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_933_);
lean_inc(v_quotContext_932_);
v___x_943_ = l_Lean_addMacroScope(v_quotContext_932_, v___x_942_, v_currMacroScope_933_);
v___x_944_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11));
lean_inc_n(v___x_939_, 2);
v___x_945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_945_, 0, v___x_939_);
lean_ctor_set(v___x_945_, 1, v___x_941_);
lean_ctor_set(v___x_945_, 2, v___x_943_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
v___x_946_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_947_ = l_Lean_Syntax_node1(v___x_939_, v___x_946_, v_val_926_);
v___x_948_ = l_Lean_Syntax_node2(v___x_939_, v___x_940_, v___x_945_, v___x_947_);
v___y_887_ = v_ver_931_;
v___y_888_ = v___y_927_;
v___y_889_ = v___y_928_;
v___y_890_ = v___y_929_;
v_quotContext_891_ = v_quotContext_932_;
v_currMacroScope_892_ = v_currMacroScope_933_;
v_ref_893_ = v_ref_934_;
v___y_894_ = v___x_936_;
v_a_895_ = v___x_948_;
v_a_896_ = v___y_935_;
goto v___jp_886_;
}
v___jp_949_:
{
if (lean_obj_tag(v___y_950_) == 1)
{
lean_object* v_val_958_; lean_object* v_quotContext_959_; lean_object* v_currMacroScope_960_; lean_object* v_ref_961_; 
v_val_958_ = lean_ctor_get(v___y_950_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___y_950_, 1);
v_quotContext_959_ = lean_ctor_get(v___y_956_, 1);
v_currMacroScope_960_ = lean_ctor_get(v___y_956_, 2);
v_ref_961_ = lean_ctor_get(v___y_956_, 5);
lean_inc(v_currMacroScope_960_);
lean_inc(v_quotContext_959_);
v_val_926_ = v_val_958_;
v___y_927_ = v___y_951_;
v___y_928_ = v___y_952_;
v___y_929_ = v___y_953_;
v___y_930_ = v___y_954_;
v_ver_931_ = v_ver_955_;
v_quotContext_932_ = v_quotContext_959_;
v_currMacroScope_933_ = v_currMacroScope_960_;
v_ref_934_ = v_ref_961_;
v___y_935_ = v___y_957_;
goto v___jp_925_;
}
else
{
lean_object* v_quotContext_962_; lean_object* v_currMacroScope_963_; lean_object* v_ref_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v___y_950_);
v_quotContext_962_ = lean_ctor_get(v___y_956_, 1);
v_currMacroScope_963_ = lean_ctor_get(v___y_956_, 2);
v_ref_964_ = lean_ctor_get(v___y_956_, 5);
v___x_965_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_954_);
v___x_966_ = 0;
v___x_967_ = l_Lean_SourceInfo_fromRef(v_ref_964_, v___x_966_);
v___x_968_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1, &l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
v___x_969_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2));
lean_inc_n(v_currMacroScope_963_, 2);
lean_inc_n(v_quotContext_962_, 2);
v___x_970_ = l_Lean_addMacroScope(v_quotContext_962_, v___x_969_, v_currMacroScope_963_);
v___x_971_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5));
v___x_972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_972_, 0, v___x_967_);
lean_ctor_set(v___x_972_, 1, v___x_968_);
lean_ctor_set(v___x_972_, 2, v___x_970_);
lean_ctor_set(v___x_972_, 3, v___x_971_);
v___y_887_ = v_ver_955_;
v___y_888_ = v___y_951_;
v___y_889_ = v___y_952_;
v___y_890_ = v___y_953_;
v_quotContext_891_ = v_quotContext_962_;
v_currMacroScope_892_ = v_currMacroScope_963_;
v_ref_893_ = v_ref_964_;
v___y_894_ = v___x_965_;
v_a_895_ = v___x_972_;
v_a_896_ = v___y_957_;
goto v___jp_886_;
}
}
v___jp_973_:
{
if (lean_obj_tag(v___y_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; 
v_a_981_ = lean_ctor_get(v___y_980_, 0);
lean_inc(v_a_981_);
v_a_982_ = lean_ctor_get(v___y_980_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___y_980_, 2);
v___y_950_ = v___y_975_;
v___y_951_ = v___y_974_;
v___y_952_ = v___y_976_;
v___y_953_ = v___y_978_;
v___y_954_ = v___y_979_;
v_ver_955_ = v_a_981_;
v___y_956_ = v___y_977_;
v___y_957_ = v_a_982_;
goto v___jp_949_;
}
else
{
lean_dec(v___y_979_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v_doc_x3f_635_);
return v___y_980_;
}
}
v___jp_983_:
{
lean_object* v_quotContext_992_; lean_object* v_currMacroScope_993_; lean_object* v_ref_994_; lean_object* v_ref_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_quotContext_992_ = lean_ctor_get(v___y_990_, 1);
v_currMacroScope_993_ = lean_ctor_get(v___y_990_, 2);
v_ref_994_ = lean_ctor_get(v___y_990_, 5);
v_ref_995_ = l_Lean_replaceRef(v___y_989_, v_ref_994_);
v___x_996_ = 0;
v___x_997_ = l_Lean_SourceInfo_fromRef(v_ref_995_, v___x_996_);
lean_dec(v_ref_995_);
v___x_998_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_999_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71);
v___x_1000_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73));
lean_inc(v_currMacroScope_993_);
lean_inc(v_quotContext_992_);
v___x_1001_ = l_Lean_addMacroScope(v_quotContext_992_, v___x_1000_, v_currMacroScope_993_);
v___x_1002_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78));
lean_inc_n(v___x_997_, 2);
v___x_1003_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_999_);
lean_ctor_set(v___x_1003_, 2, v___x_1001_);
lean_ctor_set(v___x_1003_, 3, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_1005_ = l_Lean_Syntax_node1(v___x_997_, v___x_1004_, v___y_989_);
v___x_1006_ = l_Lean_Syntax_node2(v___x_997_, v___x_998_, v___x_1003_, v___x_1005_);
v___y_950_ = v___y_985_;
v___y_951_ = v___y_984_;
v___y_952_ = v___y_986_;
v___y_953_ = v___y_987_;
v___y_954_ = v___y_988_;
v_ver_955_ = v___x_1006_;
v___y_956_ = v___y_990_;
v___y_957_ = v___y_991_;
goto v___jp_949_;
}
v___jp_1007_:
{
if (lean_obj_tag(v___y_1013_) == 1)
{
lean_object* v_val_1017_; lean_object* v_methods_1018_; lean_object* v_quotContext_1019_; lean_object* v_currMacroScope_1020_; lean_object* v_currRecDepth_1021_; lean_object* v_maxRecDepth_1022_; lean_object* v_ref_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v_ref_1026_; lean_object* v___x_1027_; 
v_val_1017_ = lean_ctor_get(v___y_1013_, 0);
lean_inc_n(v_val_1017_, 2);
lean_dec_ref_known(v___y_1013_, 1);
v_methods_1018_ = lean_ctor_get(v___y_1011_, 0);
v_quotContext_1019_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1020_ = lean_ctor_get(v___y_1011_, 2);
v_currRecDepth_1021_ = lean_ctor_get(v___y_1011_, 3);
v_maxRecDepth_1022_ = lean_ctor_get(v___y_1011_, 4);
v_ref_1023_ = lean_ctor_get(v___y_1011_, 5);
v___x_1024_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80));
v___x_1025_ = l_Lean_Syntax_isOfKind(v_val_1017_, v___x_1024_);
v_ref_1026_ = l_Lean_replaceRef(v_val_1017_, v_ref_1023_);
lean_inc(v_ref_1026_);
lean_inc(v_maxRecDepth_1022_);
lean_inc(v_currRecDepth_1021_);
lean_inc(v_currMacroScope_1020_);
lean_inc(v_quotContext_1019_);
lean_inc(v_methods_1018_);
v___x_1027_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1027_, 0, v_methods_1018_);
lean_ctor_set(v___x_1027_, 1, v_quotContext_1019_);
lean_ctor_set(v___x_1027_, 2, v_currMacroScope_1020_);
lean_ctor_set(v___x_1027_, 3, v_currRecDepth_1021_);
lean_ctor_set(v___x_1027_, 4, v_maxRecDepth_1022_);
lean_ctor_set(v___x_1027_, 5, v_ref_1026_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v_ref_1026_);
v___x_1028_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81));
v___x_1029_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1017_, v___x_1028_, v___x_1027_, v___y_1015_);
lean_dec_ref_known(v___x_1027_, 6);
lean_dec(v_val_1017_);
v___y_974_ = v___y_1008_;
v___y_975_ = v___y_1009_;
v___y_976_ = v___y_1016_;
v___y_977_ = v___y_1011_;
v___y_978_ = v___y_1012_;
v___y_979_ = v___y_1014_;
v___y_980_ = v___x_1029_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = l_Lean_Syntax_getArg(v_val_1017_, v___x_777_);
lean_inc(v___x_1030_);
v___x_1031_ = l_Lean_Syntax_matchesNull(v___x_1030_, v___x_779_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; 
v___x_1032_ = l_Lean_Syntax_matchesNull(v___x_1030_, v___x_777_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v_ref_1026_);
v___x_1033_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81));
v___x_1034_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1017_, v___x_1033_, v___x_1027_, v___y_1015_);
lean_dec_ref_known(v___x_1027_, 6);
lean_dec(v_val_1017_);
v___y_974_ = v___y_1008_;
v___y_975_ = v___y_1009_;
v___y_976_ = v___y_1016_;
v___y_977_ = v___y_1011_;
v___y_978_ = v___y_1012_;
v___y_979_ = v___y_1014_;
v___y_980_ = v___x_1034_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref_known(v___x_1027_, 6);
v___x_1035_ = l_Lean_Syntax_getArg(v_val_1017_, v___x_779_);
lean_dec(v_val_1017_);
v___x_1036_ = l_Lean_SourceInfo_fromRef(v_ref_1026_, v___x_1031_);
lean_dec(v_ref_1026_);
v___x_1037_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83));
v___x_1038_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85));
v___x_1039_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86));
lean_inc_n(v___x_1036_, 10);
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1036_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88));
v___x_1042_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90);
v___x_1043_ = lean_box(0);
lean_inc_n(v_currMacroScope_1020_, 2);
lean_inc_n(v_quotContext_1019_, 2);
v___x_1044_ = l_Lean_addMacroScope(v_quotContext_1019_, v___x_1043_, v_currMacroScope_1020_);
v___x_1045_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102));
v___x_1046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1036_);
lean_ctor_set(v___x_1046_, 1, v___x_1042_);
lean_ctor_set(v___x_1046_, 2, v___x_1044_);
lean_ctor_set(v___x_1046_, 3, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node1(v___x_1036_, v___x_1041_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node2(v___x_1036_, v___x_1038_, v___x_1040_, v___x_1047_);
v___x_1049_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104));
v___x_1050_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105));
v___x_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1036_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_Syntax_node2(v___x_1036_, v___x_1049_, v___x_1051_, v___x_1035_);
v___x_1053_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36));
v___x_1054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1036_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_1056_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106);
v___x_1057_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107));
v___x_1058_ = l_Lean_addMacroScope(v_quotContext_1019_, v___x_1057_, v_currMacroScope_1020_);
v___x_1059_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112));
v___x_1060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1036_);
lean_ctor_set(v___x_1060_, 1, v___x_1056_);
lean_ctor_set(v___x_1060_, 2, v___x_1058_);
lean_ctor_set(v___x_1060_, 3, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node1(v___x_1036_, v___x_1055_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113));
v___x_1063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1036_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_Syntax_node5(v___x_1036_, v___x_1037_, v___x_1048_, v___x_1052_, v___x_1054_, v___x_1061_, v___x_1063_);
v___y_950_ = v___y_1009_;
v___y_951_ = v___y_1008_;
v___y_952_ = v___y_1016_;
v___y_953_ = v___y_1012_;
v___y_954_ = v___y_1014_;
v_ver_955_ = v___x_1064_;
v___y_956_ = v___y_1011_;
v___y_957_ = v___y_1015_;
goto v___jp_949_;
}
}
else
{
lean_object* v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v___x_1030_);
lean_dec_ref_known(v___x_1027_, 6);
v___x_1065_ = l_Lean_Syntax_getArg(v_val_1017_, v___x_779_);
lean_dec(v_val_1017_);
v___x_1066_ = 0;
v___x_1067_ = l_Lean_SourceInfo_fromRef(v_ref_1026_, v___x_1066_);
lean_dec(v_ref_1026_);
v___x_1068_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4));
v___x_1069_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71);
v___x_1070_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73));
lean_inc(v_currMacroScope_1020_);
lean_inc(v_quotContext_1019_);
v___x_1071_ = l_Lean_addMacroScope(v_quotContext_1019_, v___x_1070_, v_currMacroScope_1020_);
v___x_1072_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78));
lean_inc_n(v___x_1067_, 2);
v___x_1073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1067_);
lean_ctor_set(v___x_1073_, 1, v___x_1069_);
lean_ctor_set(v___x_1073_, 2, v___x_1071_);
lean_ctor_set(v___x_1073_, 3, v___x_1072_);
v___x_1074_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13));
v___x_1075_ = l_Lean_Syntax_node1(v___x_1067_, v___x_1074_, v___x_1065_);
v___x_1076_ = l_Lean_Syntax_node2(v___x_1067_, v___x_1068_, v___x_1073_, v___x_1075_);
v___y_950_ = v___y_1009_;
v___y_951_ = v___y_1008_;
v___y_952_ = v___y_1016_;
v___y_953_ = v___y_1012_;
v___y_954_ = v___y_1014_;
v_ver_955_ = v___x_1076_;
v___y_956_ = v___y_1011_;
v___y_957_ = v___y_1015_;
goto v___jp_949_;
}
}
}
else
{
lean_dec(v___y_1013_);
if (lean_obj_tag(v___y_1009_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_val_1077_ = lean_ctor_get(v___y_1009_, 0);
v___x_1078_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115));
lean_inc(v_val_1077_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v_val_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v_quotContext_1080_; lean_object* v_currMacroScope_1081_; lean_object* v_ref_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_inc(v_val_1077_);
lean_dec_ref_known(v___y_1009_, 1);
v_quotContext_1080_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1081_ = lean_ctor_get(v___y_1011_, 2);
v_ref_1082_ = lean_ctor_get(v___y_1011_, 5);
v___x_1083_ = l_Lean_SourceInfo_fromRef(v_ref_1082_, v___x_1079_);
v___x_1084_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117);
v___x_1085_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc_n(v_currMacroScope_1081_, 2);
lean_inc_n(v_quotContext_1080_, 2);
v___x_1086_ = l_Lean_addMacroScope(v_quotContext_1080_, v___x_1085_, v_currMacroScope_1081_);
v___x_1087_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123));
v___x_1088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1083_);
lean_ctor_set(v___x_1088_, 1, v___x_1084_);
lean_ctor_set(v___x_1088_, 2, v___x_1086_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
v_val_926_ = v_val_1077_;
v___y_927_ = v___y_1008_;
v___y_928_ = v___y_1016_;
v___y_929_ = v___y_1012_;
v___y_930_ = v___y_1014_;
v_ver_931_ = v___x_1088_;
v_quotContext_932_ = v_quotContext_1080_;
v_currMacroScope_933_ = v_currMacroScope_1081_;
v_ref_934_ = v_ref_1082_;
v___y_935_ = v___y_1015_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = l_Lean_Syntax_getArg(v_val_1077_, v___x_777_);
v___x_1090_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125));
lean_inc(v___x_1089_);
v___x_1091_ = l_Lean_Syntax_isOfKind(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v_quotContext_1092_; lean_object* v_currMacroScope_1093_; lean_object* v_ref_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_inc(v_val_1077_);
lean_dec(v___x_1089_);
lean_dec_ref_known(v___y_1009_, 1);
v_quotContext_1092_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1093_ = lean_ctor_get(v___y_1011_, 2);
v_ref_1094_ = lean_ctor_get(v___y_1011_, 5);
v___x_1095_ = l_Lean_SourceInfo_fromRef(v_ref_1094_, v___x_1091_);
v___x_1096_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117);
v___x_1097_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc_n(v_currMacroScope_1093_, 2);
lean_inc_n(v_quotContext_1092_, 2);
v___x_1098_ = l_Lean_addMacroScope(v_quotContext_1092_, v___x_1097_, v_currMacroScope_1093_);
v___x_1099_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123));
v___x_1100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1095_);
lean_ctor_set(v___x_1100_, 1, v___x_1096_);
lean_ctor_set(v___x_1100_, 2, v___x_1098_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
v_val_926_ = v_val_1077_;
v___y_927_ = v___y_1008_;
v___y_928_ = v___y_1016_;
v___y_929_ = v___y_1012_;
v___y_930_ = v___y_1014_;
v_ver_931_ = v___x_1100_;
v_quotContext_932_ = v_quotContext_1092_;
v_currMacroScope_933_ = v_currMacroScope_1093_;
v_ref_934_ = v_ref_1094_;
v___y_935_ = v___y_1015_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = l_Lean_Syntax_getArg(v___x_1089_, v___y_1012_);
lean_inc(v___x_1101_);
v___x_1102_ = l_Lean_Syntax_matchesNull(v___x_1101_, v___y_1012_);
if (v___x_1102_ == 0)
{
lean_object* v_quotContext_1103_; lean_object* v_currMacroScope_1104_; lean_object* v_ref_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc(v_val_1077_);
lean_dec(v___x_1101_);
lean_dec(v___x_1089_);
lean_dec_ref_known(v___y_1009_, 1);
v_quotContext_1103_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1104_ = lean_ctor_get(v___y_1011_, 2);
v_ref_1105_ = lean_ctor_get(v___y_1011_, 5);
v___x_1106_ = l_Lean_SourceInfo_fromRef(v_ref_1105_, v___x_1102_);
v___x_1107_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117);
v___x_1108_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc_n(v_currMacroScope_1104_, 2);
lean_inc_n(v_quotContext_1103_, 2);
v___x_1109_ = l_Lean_addMacroScope(v_quotContext_1103_, v___x_1108_, v_currMacroScope_1104_);
v___x_1110_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123));
v___x_1111_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1106_);
lean_ctor_set(v___x_1111_, 1, v___x_1107_);
lean_ctor_set(v___x_1111_, 2, v___x_1109_);
lean_ctor_set(v___x_1111_, 3, v___x_1110_);
v_val_926_ = v_val_1077_;
v___y_927_ = v___y_1008_;
v___y_928_ = v___y_1016_;
v___y_929_ = v___y_1012_;
v___y_930_ = v___y_1014_;
v_ver_931_ = v___x_1111_;
v_quotContext_932_ = v_quotContext_1103_;
v_currMacroScope_933_ = v_currMacroScope_1104_;
v_ref_934_ = v_ref_1105_;
v___y_935_ = v___y_1015_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = l_Lean_Syntax_getArg(v___x_1101_, v___x_779_);
lean_dec(v___x_1101_);
v___x_1113_ = l_Lean_Syntax_getArg(v___x_1089_, v___y_1010_);
lean_dec(v___x_1089_);
v___x_1114_ = l_Lean_Syntax_isNone(v___x_1113_);
if (v___x_1114_ == 0)
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_Syntax_matchesNull(v___x_1113_, v___y_1012_);
if (v___x_1115_ == 0)
{
lean_object* v_quotContext_1116_; lean_object* v_currMacroScope_1117_; lean_object* v_ref_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_inc(v_val_1077_);
lean_dec(v___x_1112_);
lean_dec_ref_known(v___y_1009_, 1);
v_quotContext_1116_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1117_ = lean_ctor_get(v___y_1011_, 2);
v_ref_1118_ = lean_ctor_get(v___y_1011_, 5);
v___x_1119_ = l_Lean_SourceInfo_fromRef(v_ref_1118_, v___x_1115_);
v___x_1120_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117);
v___x_1121_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc_n(v_currMacroScope_1117_, 2);
lean_inc_n(v_quotContext_1116_, 2);
v___x_1122_ = l_Lean_addMacroScope(v_quotContext_1116_, v___x_1121_, v_currMacroScope_1117_);
v___x_1123_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123));
v___x_1124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1119_);
lean_ctor_set(v___x_1124_, 1, v___x_1120_);
lean_ctor_set(v___x_1124_, 2, v___x_1122_);
lean_ctor_set(v___x_1124_, 3, v___x_1123_);
v_val_926_ = v_val_1077_;
v___y_927_ = v___y_1008_;
v___y_928_ = v___y_1016_;
v___y_929_ = v___y_1012_;
v___y_930_ = v___y_1014_;
v_ver_931_ = v___x_1124_;
v_quotContext_932_ = v_quotContext_1116_;
v_currMacroScope_933_ = v_currMacroScope_1117_;
v_ref_934_ = v_ref_1118_;
v___y_935_ = v___y_1015_;
goto v___jp_925_;
}
else
{
v___y_984_ = v___y_1008_;
v___y_985_ = v___y_1009_;
v___y_986_ = v___y_1016_;
v___y_987_ = v___y_1012_;
v___y_988_ = v___y_1014_;
v___y_989_ = v___x_1112_;
v___y_990_ = v___y_1011_;
v___y_991_ = v___y_1015_;
goto v___jp_983_;
}
}
else
{
lean_dec(v___x_1113_);
v___y_984_ = v___y_1008_;
v___y_985_ = v___y_1009_;
v___y_986_ = v___y_1016_;
v___y_987_ = v___y_1012_;
v___y_988_ = v___y_1014_;
v___y_989_ = v___x_1112_;
v___y_990_ = v___y_1011_;
v___y_991_ = v___y_1015_;
goto v___jp_983_;
}
}
}
}
}
else
{
lean_object* v_quotContext_1125_; lean_object* v_currMacroScope_1126_; lean_object* v_ref_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_quotContext_1125_ = lean_ctor_get(v___y_1011_, 1);
v_currMacroScope_1126_ = lean_ctor_get(v___y_1011_, 2);
v_ref_1127_ = lean_ctor_get(v___y_1011_, 5);
v___x_1128_ = 0;
v___x_1129_ = l_Lean_SourceInfo_fromRef(v_ref_1127_, v___x_1128_);
v___x_1130_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117);
v___x_1131_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118));
lean_inc(v_currMacroScope_1126_);
lean_inc(v_quotContext_1125_);
v___x_1132_ = l_Lean_addMacroScope(v_quotContext_1125_, v___x_1131_, v_currMacroScope_1126_);
v___x_1133_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123));
v___x_1134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1129_);
lean_ctor_set(v___x_1134_, 1, v___x_1130_);
lean_ctor_set(v___x_1134_, 2, v___x_1132_);
lean_ctor_set(v___x_1134_, 3, v___x_1133_);
v___y_950_ = v___y_1009_;
v___y_951_ = v___y_1008_;
v___y_952_ = v___y_1016_;
v___y_953_ = v___y_1012_;
v___y_954_ = v___y_1014_;
v_ver_955_ = v___x_1134_;
v___y_956_ = v___y_1011_;
v___y_957_ = v___y_1015_;
goto v___jp_949_;
}
}
}
v___jp_1135_:
{
uint8_t v___x_1144_; 
lean_inc(v___x_778_);
v___x_1144_ = l_Lean_Syntax_isOfKind(v___x_778_, v___y_1138_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v_a_1142_);
lean_dec(v___y_1141_);
lean_dec(v___y_1136_);
lean_dec(v_doc_x3f_635_);
v___x_1145_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__126));
v___x_1146_ = l_Lean_Macro_throwErrorAt___redArg(v___x_778_, v___x_1145_, v___y_1137_, v_a_1143_);
lean_dec(v___x_778_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = l_Lean_Syntax_getArg(v___x_778_, v___x_777_);
v___x_1148_ = l_Lean_Syntax_isNone(v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; 
lean_inc(v___x_1147_);
v___x_1149_ = l_Lean_Syntax_matchesNull(v___x_1147_, v___y_1140_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_1147_);
lean_dec(v_a_1142_);
lean_dec(v___y_1141_);
lean_dec(v___y_1136_);
lean_dec(v_doc_x3f_635_);
v___x_1150_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__126));
v___x_1151_ = l_Lean_Macro_throwErrorAt___redArg(v___x_778_, v___x_1150_, v___y_1137_, v_a_1143_);
lean_dec(v___x_778_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = l_Lean_Syntax_getArg(v___x_1147_, v___x_777_);
lean_dec(v___x_1147_);
v___x_1153_ = l_Lean_Syntax_getArg(v___x_778_, v___x_779_);
lean_dec(v___x_778_);
v___y_1008_ = v___y_1136_;
v___y_1009_ = v_a_1142_;
v___y_1010_ = v___y_1139_;
v___y_1011_ = v___y_1137_;
v___y_1012_ = v___y_1140_;
v___y_1013_ = v___y_1141_;
v___y_1014_ = v___x_1153_;
v___y_1015_ = v_a_1143_;
v___y_1016_ = v___x_1152_;
goto v___jp_1007_;
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v___x_1147_);
v___x_1154_ = l_Lean_Syntax_getArg(v___x_778_, v___x_779_);
v___x_1155_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89));
v___x_1156_ = 0;
v___x_1157_ = l_Lean_SourceInfo_fromRef(v___x_778_, v___x_1156_);
lean_dec(v___x_778_);
v___x_1158_ = l_Lean_Syntax_mkStrLit(v___x_1155_, v___x_1157_);
v___y_1008_ = v___y_1136_;
v___y_1009_ = v_a_1142_;
v___y_1010_ = v___y_1139_;
v___y_1011_ = v___y_1137_;
v___y_1012_ = v___y_1140_;
v___y_1013_ = v___y_1141_;
v___y_1014_ = v___x_1154_;
v___y_1015_ = v_a_1143_;
v___y_1016_ = v___x_1158_;
goto v___jp_1007_;
}
}
}
v___jp_1159_:
{
if (lean_obj_tag(v___y_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_a_1168_; lean_object* v___x_1169_; 
v_a_1167_ = lean_ctor_get(v___y_1166_, 0);
lean_inc(v_a_1167_);
v_a_1168_ = lean_ctor_get(v___y_1166_, 1);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___y_1166_, 2);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_a_1167_);
v___y_1136_ = v___y_1160_;
v___y_1137_ = v___y_1161_;
v___y_1138_ = v___y_1163_;
v___y_1139_ = v___y_1162_;
v___y_1140_ = v___y_1164_;
v___y_1141_ = v___y_1165_;
v_a_1142_ = v___x_1169_;
v_a_1143_ = v_a_1168_;
goto v___jp_1135_;
}
else
{
lean_dec(v___y_1165_);
lean_dec(v___y_1160_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
return v___y_1166_;
}
}
v___jp_1170_:
{
lean_object* v___x_1178_; 
v___x_1178_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__128));
if (lean_obj_tag(v___y_1175_) == 0)
{
v___y_1136_ = v_opts_x3f_1177_;
v___y_1137_ = v___y_1176_;
v___y_1138_ = v___x_1178_;
v___y_1139_ = v___y_1171_;
v___y_1140_ = v___y_1173_;
v___y_1141_ = v___y_1174_;
v_a_1142_ = v___y_1175_;
v_a_1143_ = v___y_1172_;
goto v___jp_1135_;
}
else
{
lean_object* v_val_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1224_; 
v_val_1179_ = lean_ctor_get(v___y_1175_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___y_1175_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1181_ = v___y_1175_;
v_isShared_1182_ = v_isSharedCheck_1224_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_val_1179_);
lean_dec(v___y_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1224_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115));
lean_inc(v_val_1179_);
v___x_1184_ = l_Lean_Syntax_isOfKind(v_val_1179_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_del_object(v___x_1181_);
v___x_1185_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4));
v___x_1186_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1179_, v___x_1185_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1186_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1187_ = l_Lean_Syntax_getArg(v_val_1179_, v___x_777_);
v___x_1188_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__125));
lean_inc(v___x_1187_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__130));
lean_inc(v___x_1187_);
v___x_1191_ = l_Lean_Syntax_isOfKind(v___x_1187_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v___x_1187_);
lean_del_object(v___x_1181_);
v___x_1192_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4));
v___x_1193_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1179_, v___x_1192_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1193_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = l_Lean_Syntax_getArg(v___x_1187_, v___x_777_);
v___x_1195_ = l_Lean_Syntax_isNone(v___x_1194_);
if (v___x_1195_ == 0)
{
uint8_t v___x_1196_; 
lean_inc(v___x_1194_);
v___x_1196_ = l_Lean_Syntax_matchesNull(v___x_1194_, v___x_779_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v___x_1194_);
lean_dec(v___x_1187_);
lean_del_object(v___x_1181_);
v___x_1197_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4));
v___x_1198_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1179_, v___x_1197_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1198_;
goto v___jp_1159_;
}
else
{
lean_object* v_copyTk_x3f_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_copyTk_x3f_1199_ = l_Lean_Syntax_getArg(v___x_1194_, v___x_777_);
lean_dec(v___x_1194_);
v___x_1200_ = lean_box(0);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_copyTk_x3f_1199_);
v___x_1202_ = v___x_1181_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_copyTk_x3f_1199_);
v___x_1202_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_1187_, v___x_779_, v_val_1179_, v___x_1189_, v___x_772_, v___x_1200_, v___x_1202_, v___y_1176_, v___y_1172_);
lean_dec_ref(v___x_1202_);
lean_dec(v_val_1179_);
lean_dec(v___x_1187_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1203_;
goto v___jp_1159_;
}
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v___x_1194_);
lean_del_object(v___x_1181_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_box(0);
v___x_1207_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(v___x_1187_, v___x_779_, v_val_1179_, v___x_1189_, v___x_772_, v___x_1205_, v___x_1206_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
lean_dec(v___x_1187_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1207_;
goto v___jp_1159_;
}
}
}
else
{
lean_object* v_tk_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_tk_1208_ = l_Lean_Syntax_getArg(v___x_1187_, v___x_777_);
v___x_1209_ = l_Lean_Syntax_getArg(v___x_1187_, v___x_779_);
v___x_1210_ = l_Lean_Syntax_getArg(v___x_1187_, v___y_1173_);
v___x_1211_ = l_Lean_Syntax_isNone(v___x_1210_);
if (v___x_1211_ == 0)
{
uint8_t v___x_1212_; 
lean_inc(v___x_1210_);
v___x_1212_ = l_Lean_Syntax_matchesNull(v___x_1210_, v___y_1173_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v___x_1210_);
lean_dec(v___x_1209_);
lean_dec(v_tk_1208_);
lean_dec(v___x_1187_);
lean_del_object(v___x_1181_);
v___x_1213_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1___closed__4));
v___x_1214_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1179_, v___x_1213_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1214_;
goto v___jp_1159_;
}
else
{
lean_object* v_rev_x3f_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v_rev_x3f_1215_ = l_Lean_Syntax_getArg(v___x_1210_, v___x_779_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_rev_x3f_1215_);
v___x_1218_ = v___x_1181_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_rev_x3f_1215_);
v___x_1218_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1(v___x_772_, v___x_1209_, v_tk_1208_, v___x_1187_, v___y_1171_, v___y_1173_, v_val_1179_, v___x_779_, v___x_1216_, v___x_1218_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
lean_dec(v___x_1187_);
lean_dec(v_tk_1208_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1219_;
goto v___jp_1159_;
}
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec(v___x_1210_);
lean_del_object(v___x_1181_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_box(0);
v___x_1223_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__1(v___x_772_, v___x_1209_, v_tk_1208_, v___x_1187_, v___y_1171_, v___y_1173_, v_val_1179_, v___x_779_, v___x_1221_, v___x_1222_, v___y_1176_, v___y_1172_);
lean_dec(v_val_1179_);
lean_dec(v___x_1187_);
lean_dec(v_tk_1208_);
v___y_1160_ = v_opts_x3f_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___y_1173_;
v___y_1165_ = v___y_1174_;
v___y_1166_ = v___x_1223_;
goto v___jp_1159_;
}
}
}
}
}
}
v___jp_1225_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = lean_unsigned_to_nat(3u);
v___x_1232_ = l_Lean_Syntax_getArg(v_stx_634_, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_isNone(v___x_1232_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
lean_inc(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_matchesNull(v___x_1232_, v___x_779_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v___x_1232_);
lean_dec(v_src_x3f_1230_);
lean_dec(v___y_1228_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1235_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1236_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1235_, v___y_1229_, v___y_1227_);
lean_dec(v_stx_634_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = l_Lean_Syntax_getArg(v___x_1232_, v___x_777_);
lean_dec(v___x_1232_);
v___x_1238_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__132));
lean_inc(v___x_1237_);
v___x_1239_ = l_Lean_Syntax_isOfKind(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec(v___x_1237_);
lean_dec(v_src_x3f_1230_);
lean_dec(v___y_1228_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1240_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1241_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1240_, v___y_1229_, v___y_1227_);
lean_dec(v_stx_634_);
return v___x_1241_;
}
else
{
lean_object* v_opts_x3f_1242_; lean_object* v___x_1243_; 
lean_dec(v_stx_634_);
v_opts_x3f_1242_ = l_Lean_Syntax_getArg(v___x_1237_, v___x_779_);
lean_dec(v___x_1237_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_opts_x3f_1242_);
v___y_1171_ = v___x_1231_;
v___y_1172_ = v___y_1227_;
v___y_1173_ = v___y_1226_;
v___y_1174_ = v___y_1228_;
v___y_1175_ = v_src_x3f_1230_;
v___y_1176_ = v___y_1229_;
v_opts_x3f_1177_ = v___x_1243_;
goto v___jp_1170_;
}
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v___x_1232_);
lean_dec(v_stx_634_);
v___x_1244_ = lean_box(0);
v___y_1171_ = v___x_1231_;
v___y_1172_ = v___y_1227_;
v___y_1173_ = v___y_1226_;
v___y_1174_ = v___y_1228_;
v___y_1175_ = v_src_x3f_1230_;
v___y_1176_ = v___y_1229_;
v_opts_x3f_1177_ = v___x_1244_;
goto v___jp_1170_;
}
}
v___jp_1245_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_unsigned_to_nat(2u);
v___x_1250_ = l_Lean_Syntax_getArg(v_stx_634_, v___x_1249_);
v___x_1251_ = l_Lean_Syntax_isNone(v___x_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
lean_inc(v___x_1250_);
v___x_1252_ = l_Lean_Syntax_matchesNull(v___x_1250_, v___x_779_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v___x_1250_);
lean_dec(v_ver_x3f_1246_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1253_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1254_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1253_, v___y_1247_, v___y_1248_);
lean_dec(v_stx_634_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = l_Lean_Syntax_getArg(v___x_1250_, v___x_777_);
lean_dec(v___x_1250_);
v___x_1256_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__134));
lean_inc(v___x_1255_);
v___x_1257_ = l_Lean_Syntax_isOfKind(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v___x_1255_);
lean_dec(v_ver_x3f_1246_);
lean_dec(v___x_778_);
lean_dec(v_doc_x3f_635_);
v___x_1258_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19));
v___x_1259_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_634_, v___x_1258_, v___y_1247_, v___y_1248_);
lean_dec(v_stx_634_);
return v___x_1259_;
}
else
{
lean_object* v_src_x3f_1260_; lean_object* v___x_1261_; 
v_src_x3f_1260_ = l_Lean_Syntax_getArg(v___x_1255_, v___x_779_);
lean_dec(v___x_1255_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_src_x3f_1260_);
v___y_1226_ = v___x_1249_;
v___y_1227_ = v___y_1248_;
v___y_1228_ = v_ver_x3f_1246_;
v___y_1229_ = v___y_1247_;
v_src_x3f_1230_ = v___x_1261_;
goto v___jp_1225_;
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v___x_1250_);
v___x_1262_ = lean_box(0);
v___y_1226_ = v___x_1249_;
v___y_1227_ = v___y_1248_;
v___y_1228_ = v_ver_x3f_1246_;
v___y_1229_ = v___y_1247_;
v_src_x3f_1230_ = v___x_1262_;
goto v___jp_1225_;
}
}
}
v___jp_638_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_inc_n(v___y_655_, 8);
lean_inc(v___y_653_);
lean_inc_n(v___y_662_, 9);
v___x_667_ = l_Lean_Syntax_node3(v___y_662_, v___y_664_, v___y_653_, v___y_655_, v___y_666_);
lean_inc_n(v___y_661_, 2);
v___x_668_ = l_Lean_Syntax_node3(v___y_662_, v___y_661_, v___y_655_, v___y_655_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node2(v___y_662_, v___y_652_, v___y_660_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(10u);
v___x_671_ = lean_mk_empty_array_with_capacity(v___x_670_);
v___x_672_ = lean_array_push(v___x_671_, v___y_659_);
lean_inc_n(v___y_644_, 4);
v___x_673_ = lean_array_push(v___x_672_, v___y_644_);
v___x_674_ = lean_array_push(v___x_673_, v___y_639_);
v___x_675_ = lean_array_push(v___x_674_, v___y_644_);
v___x_676_ = lean_array_push(v___x_675_, v___y_651_);
v___x_677_ = lean_array_push(v___x_676_, v___y_644_);
v___x_678_ = lean_array_push(v___x_677_, v___y_647_);
v___x_679_ = lean_array_push(v___x_678_, v___y_644_);
v___x_680_ = lean_array_push(v___x_679_, v___x_669_);
v___x_681_ = lean_array_push(v___x_680_, v___y_644_);
v___x_682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_682_, 0, v___y_662_);
lean_ctor_set(v___x_682_, 1, v___y_661_);
lean_ctor_set(v___x_682_, 2, v___x_681_);
v___x_683_ = l_Lean_Syntax_node1(v___y_662_, v___y_657_, v___x_682_);
v___x_684_ = l_Lean_Syntax_node6(v___y_662_, v___y_663_, v___y_649_, v___y_655_, v___x_683_, v___y_645_, v___y_655_, v___y_641_);
v___x_685_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0));
v___x_686_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1));
lean_inc_ref(v___y_650_);
lean_inc_ref(v___y_642_);
v___x_687_ = l_Lean_Name_mkStr4(v___y_642_, v___y_650_, v___x_685_, v___x_686_);
v___x_688_ = l_Lean_Syntax_node2(v___y_662_, v___x_687_, v___y_655_, v___y_655_);
v___x_689_ = l_Lean_Syntax_node4(v___y_662_, v___y_658_, v___y_653_, v___x_684_, v___x_688_, v___y_655_);
v___x_690_ = l_Lean_Syntax_node5(v___y_662_, v___y_656_, v___y_665_, v___y_648_, v___y_643_, v___x_689_, v___y_655_);
lean_inc(v___y_654_);
v___x_691_ = l_Lean_Syntax_node2(v___y_662_, v___y_654_, v___y_646_, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_640_);
return v___x_692_;
}
v___jp_693_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_inc_n(v___y_712_, 16);
lean_inc_n(v___y_706_, 4);
lean_inc_n(v___y_722_, 4);
lean_inc_n(v___y_721_, 21);
v___x_727_ = l_Lean_Syntax_node3(v___y_721_, v___y_722_, v___y_706_, v___y_712_, v___y_726_);
lean_inc_n(v___y_718_, 4);
v___x_728_ = l_Lean_Syntax_node3(v___y_721_, v___y_718_, v___y_712_, v___y_712_, v___x_727_);
lean_inc_n(v___y_705_, 4);
v___x_729_ = l_Lean_Syntax_node2(v___y_721_, v___y_705_, v___y_694_, v___x_728_);
v___x_730_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___y_721_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4);
v___x_733_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5));
lean_inc_n(v___y_711_, 3);
lean_inc_n(v___y_723_, 3);
v___x_734_ = l_Lean_addMacroScope(v___y_723_, v___x_733_, v___y_711_);
lean_inc_n(v___y_725_, 3);
v___x_735_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_735_, 0, v___y_721_);
lean_ctor_set(v___x_735_, 1, v___x_732_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
lean_ctor_set(v___x_735_, 3, v___y_725_);
lean_inc_n(v___y_714_, 3);
v___x_736_ = l_Lean_Syntax_node2(v___y_721_, v___y_714_, v___x_735_, v___y_712_);
v___x_737_ = l_Lean_Syntax_node3(v___y_721_, v___y_722_, v___y_706_, v___y_712_, v___y_695_);
v___x_738_ = l_Lean_Syntax_node3(v___y_721_, v___y_718_, v___y_712_, v___y_712_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node2(v___y_721_, v___y_705_, v___x_736_, v___x_738_);
v___x_740_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6));
v___x_741_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7);
v___x_742_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8));
v___x_743_ = l_Lean_addMacroScope(v___y_723_, v___x_742_, v___y_711_);
lean_inc_ref(v___y_708_);
lean_inc_ref(v___y_704_);
lean_inc_ref_n(v___y_697_, 2);
v___x_744_ = l_Lean_Name_mkStr4(v___y_697_, v___y_704_, v___y_708_, v___x_740_);
v___x_745_ = lean_box(0);
lean_inc(v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_744_);
v___x_748_ = l_Lean_Name_mkStr2(v___y_697_, v___x_740_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___y_725_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_747_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_746_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_753_, 0, v___y_721_);
lean_ctor_set(v___x_753_, 1, v___x_741_);
lean_ctor_set(v___x_753_, 2, v___x_743_);
lean_ctor_set(v___x_753_, 3, v___x_752_);
v___x_754_ = l_Lean_Syntax_node2(v___y_721_, v___y_714_, v___x_753_, v___y_712_);
v___x_755_ = l_Lean_Syntax_node3(v___y_721_, v___y_722_, v___y_706_, v___y_712_, v___y_719_);
v___x_756_ = l_Lean_Syntax_node3(v___y_721_, v___y_718_, v___y_712_, v___y_712_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node2(v___y_721_, v___y_705_, v___x_754_, v___x_756_);
v___x_758_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10);
v___x_759_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11));
v___x_760_ = l_Lean_addMacroScope(v___y_723_, v___x_759_, v___y_711_);
v___x_761_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_761_, 0, v___y_721_);
lean_ctor_set(v___x_761_, 1, v___x_758_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
lean_ctor_set(v___x_761_, 3, v___y_725_);
v___x_762_ = l_Lean_Syntax_node2(v___y_721_, v___y_714_, v___x_761_, v___y_712_);
v___x_763_ = l_Lean_Syntax_node3(v___y_721_, v___y_722_, v___y_706_, v___y_712_, v___y_709_);
v___x_764_ = l_Lean_Syntax_node3(v___y_721_, v___y_718_, v___y_712_, v___y_712_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v___y_721_, v___y_705_, v___x_762_, v___x_764_);
v___x_766_ = lean_obj_once(&l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13, &l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_once, _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13);
v___x_767_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14));
v___x_768_ = l_Lean_addMacroScope(v___y_723_, v___x_767_, v___y_711_);
v___x_769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_769_, 0, v___y_721_);
lean_ctor_set(v___x_769_, 1, v___x_766_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
lean_ctor_set(v___x_769_, 3, v___y_725_);
v___x_770_ = l_Lean_Syntax_node2(v___y_721_, v___y_714_, v___x_769_, v___y_712_);
if (lean_obj_tag(v___y_717_) == 0)
{
v___y_639_ = v___x_739_;
v___y_640_ = v___y_696_;
v___y_641_ = v___y_698_;
v___y_642_ = v___y_697_;
v___y_643_ = v___y_699_;
v___y_644_ = v___x_731_;
v___y_645_ = v___y_700_;
v___y_646_ = v___y_701_;
v___y_647_ = v___x_765_;
v___y_648_ = v___y_702_;
v___y_649_ = v___y_703_;
v___y_650_ = v___y_704_;
v___y_651_ = v___x_757_;
v___y_652_ = v___y_705_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_707_;
v___y_655_ = v___y_712_;
v___y_656_ = v___y_713_;
v___y_657_ = v___y_715_;
v___y_658_ = v___y_716_;
v___y_659_ = v___x_729_;
v___y_660_ = v___x_770_;
v___y_661_ = v___y_718_;
v___y_662_ = v___y_721_;
v___y_663_ = v___y_720_;
v___y_664_ = v___y_722_;
v___y_665_ = v___y_724_;
v___y_666_ = v___y_710_;
goto v___jp_638_;
}
else
{
lean_object* v_val_771_; 
lean_dec(v___y_710_);
v_val_771_ = lean_ctor_get(v___y_717_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___y_717_, 1);
v___y_639_ = v___x_739_;
v___y_640_ = v___y_696_;
v___y_641_ = v___y_698_;
v___y_642_ = v___y_697_;
v___y_643_ = v___y_699_;
v___y_644_ = v___x_731_;
v___y_645_ = v___y_700_;
v___y_646_ = v___y_701_;
v___y_647_ = v___x_765_;
v___y_648_ = v___y_702_;
v___y_649_ = v___y_703_;
v___y_650_ = v___y_704_;
v___y_651_ = v___x_757_;
v___y_652_ = v___y_705_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_707_;
v___y_655_ = v___y_712_;
v___y_656_ = v___y_713_;
v___y_657_ = v___y_715_;
v___y_658_ = v___y_716_;
v___y_659_ = v___x_729_;
v___y_660_ = v___x_770_;
v___y_661_ = v___y_718_;
v___y_662_ = v___y_721_;
v___y_663_ = v___y_720_;
v___y_664_ = v___y_722_;
v___y_665_ = v___y_724_;
v___y_666_ = v_val_771_;
goto v___jp_638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___boxed(lean_object* v_stx_1276_, lean_object* v_doc_x3f_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(v_stx_1276_, v_doc_x3f_1277_, v_a_1278_, v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(lean_object* v_stx_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
lean_inc(v_stx_1287_);
v___x_1291_ = l_Lean_Syntax_isOfKind(v_stx_1287_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2));
v___x_1293_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1287_, v___x_1292_, v_a_1288_, v_a_1289_);
lean_dec(v_stx_1287_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_kw_1297_; lean_object* v___x_1298_; lean_object* v_spec_1299_; lean_object* v___y_1301_; lean_object* v___x_1329_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Lean_Syntax_getArg(v_stx_1287_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(1u);
v_kw_1297_ = l_Lean_Syntax_getArg(v_stx_1287_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(2u);
v_spec_1299_ = l_Lean_Syntax_getArg(v_stx_1287_, v___x_1298_);
lean_dec(v_stx_1287_);
v___x_1329_ = l_Lean_Syntax_getOptional_x3f(v___x_1295_);
lean_dec(v___x_1295_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_box(0);
v___y_1301_ = v___x_1330_;
goto v___jp_1300_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1329_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v___y_1301_ = v___x_1336_;
goto v___jp_1300_;
}
}
}
v___jp_1300_:
{
lean_object* v_methods_1302_; lean_object* v_quotContext_1303_; lean_object* v_currMacroScope_1304_; lean_object* v_currRecDepth_1305_; lean_object* v_maxRecDepth_1306_; lean_object* v_ref_1307_; lean_object* v_ref_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_methods_1302_ = lean_ctor_get(v_a_1288_, 0);
v_quotContext_1303_ = lean_ctor_get(v_a_1288_, 1);
v_currMacroScope_1304_ = lean_ctor_get(v_a_1288_, 2);
v_currRecDepth_1305_ = lean_ctor_get(v_a_1288_, 3);
v_maxRecDepth_1306_ = lean_ctor_get(v_a_1288_, 4);
v_ref_1307_ = lean_ctor_get(v_a_1288_, 5);
v_ref_1308_ = l_Lean_replaceRef(v_kw_1297_, v_ref_1307_);
lean_dec(v_kw_1297_);
lean_inc(v_maxRecDepth_1306_);
lean_inc(v_currRecDepth_1305_);
lean_inc(v_currMacroScope_1304_);
lean_inc(v_quotContext_1303_);
lean_inc(v_methods_1302_);
v___x_1309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1309_, 0, v_methods_1302_);
lean_ctor_set(v___x_1309_, 1, v_quotContext_1303_);
lean_ctor_set(v___x_1309_, 2, v_currMacroScope_1304_);
lean_ctor_set(v___x_1309_, 3, v_currRecDepth_1305_);
lean_ctor_set(v___x_1309_, 4, v_maxRecDepth_1306_);
lean_ctor_set(v___x_1309_, 5, v_ref_1308_);
v___x_1310_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(v_spec_1299_, v___y_1301_, v___x_1309_, v_a_1289_);
lean_dec_ref_known(v___x_1309_, 6);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_a_1312_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1310_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1311_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1320_ = lean_ctor_get(v___x_1310_, 0);
v_a_1321_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1310_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_inc(v_a_1320_);
lean_dec(v___x_1310_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed(lean_object* v_stx_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(v_stx_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1(){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1371_ = l_Lean_Elab_macroAttribute;
v___x_1372_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1));
v___x_1373_ = ((lean_object*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10));
v___x_1374_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed), 3, 0);
v___x_1375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1371_, v___x_1372_, v___x_1373_, v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___boxed(lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
return v_res_1377_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Require(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
