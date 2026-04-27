// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Repeat
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Lean.Elab.BuiltinDo.For
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
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__5_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__10_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoRepeat___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__12;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__13_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Loop.mk"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoRepeat___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__18;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Loop"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 134, 225, 236, 222, 42, 27, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value),LEAN_SCALAR_PTR_LITERAL(121, 43, 2, 225, 80, 67, 164, 196)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__19_value),LEAN_SCALAR_PTR_LITERAL(244, 180, 170, 243, 159, 48, 205, 98)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value),LEAN_SCALAR_PTR_LITERAL(92, 204, 229, 77, 211, 121, 59, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__23 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__24 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__25 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__23_value),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__26 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__26_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__27 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoRepeat"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 84, 114, 24, 25, 111, 206, 161)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 265, .m_capacity = 265, .m_length = 264, .m_data = "Builtin do-element elaborator for `repeat` (syntax kind `Lean.Parser.Term.doRepeat`).\n\nExpands to `for _ in Loop.mk do ...`. A follow-up change will extend this\nelaborator to choose between `Loop.mk` and a well-founded `Repeat.mk` based on a\nconfiguration option.\n"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doWhileH"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 71, 80, 200, 0, 52, 171, 166)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__5_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__10_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__12 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhileH___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__15_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhileH___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_Lean_Elab_Do_expandDoWhileH___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhileH___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhileH(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhileH___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expandDoWhileH"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 170, 236, 219, 1, 32, 203, 49)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doWhile"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 22, 162, 157, 218, 80, 50, 216)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expandDoWhile"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 131, 102, 139, 244, 244, 13, 233)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doRepeatUntil"};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 11, 184, 16, 157, 182, 78, 231)}};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expandDoRepeatUntil"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 179, 171, 246, 163, 234, 148, 58)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(lean_object* v_00_u03b1_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(v_00_u03b1_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object* v___x_29_, lean_object* v_dec_30_, uint8_t v___x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_fileName_40_; lean_object* v_fileMap_41_; lean_object* v_options_42_; lean_object* v_currRecDepth_43_; lean_object* v_maxRecDepth_44_; lean_object* v_ref_45_; lean_object* v_currNamespace_46_; lean_object* v_openDecls_47_; lean_object* v_initHeartbeats_48_; lean_object* v_maxHeartbeats_49_; lean_object* v_quotContext_50_; lean_object* v_currMacroScope_51_; uint8_t v_diag_52_; lean_object* v_cancelTk_x3f_53_; uint8_t v_suppressElabErrors_54_; lean_object* v_inheritedTraceOptions_55_; lean_object* v_ref_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_fileName_40_ = lean_ctor_get(v___y_37_, 0);
v_fileMap_41_ = lean_ctor_get(v___y_37_, 1);
v_options_42_ = lean_ctor_get(v___y_37_, 2);
v_currRecDepth_43_ = lean_ctor_get(v___y_37_, 3);
v_maxRecDepth_44_ = lean_ctor_get(v___y_37_, 4);
v_ref_45_ = lean_ctor_get(v___y_37_, 5);
v_currNamespace_46_ = lean_ctor_get(v___y_37_, 6);
v_openDecls_47_ = lean_ctor_get(v___y_37_, 7);
v_initHeartbeats_48_ = lean_ctor_get(v___y_37_, 8);
v_maxHeartbeats_49_ = lean_ctor_get(v___y_37_, 9);
v_quotContext_50_ = lean_ctor_get(v___y_37_, 10);
v_currMacroScope_51_ = lean_ctor_get(v___y_37_, 11);
v_diag_52_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*14);
v_cancelTk_x3f_53_ = lean_ctor_get(v___y_37_, 12);
v_suppressElabErrors_54_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_55_ = lean_ctor_get(v___y_37_, 13);
v_ref_56_ = l_Lean_replaceRef(v___x_29_, v_ref_45_);
lean_inc_ref(v_inheritedTraceOptions_55_);
lean_inc(v_cancelTk_x3f_53_);
lean_inc(v_currMacroScope_51_);
lean_inc(v_quotContext_50_);
lean_inc(v_maxHeartbeats_49_);
lean_inc(v_initHeartbeats_48_);
lean_inc(v_openDecls_47_);
lean_inc(v_currNamespace_46_);
lean_inc(v_maxRecDepth_44_);
lean_inc(v_currRecDepth_43_);
lean_inc_ref(v_options_42_);
lean_inc_ref(v_fileMap_41_);
lean_inc_ref(v_fileName_40_);
v___x_57_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_57_, 0, v_fileName_40_);
lean_ctor_set(v___x_57_, 1, v_fileMap_41_);
lean_ctor_set(v___x_57_, 2, v_options_42_);
lean_ctor_set(v___x_57_, 3, v_currRecDepth_43_);
lean_ctor_set(v___x_57_, 4, v_maxRecDepth_44_);
lean_ctor_set(v___x_57_, 5, v_ref_56_);
lean_ctor_set(v___x_57_, 6, v_currNamespace_46_);
lean_ctor_set(v___x_57_, 7, v_openDecls_47_);
lean_ctor_set(v___x_57_, 8, v_initHeartbeats_48_);
lean_ctor_set(v___x_57_, 9, v_maxHeartbeats_49_);
lean_ctor_set(v___x_57_, 10, v_quotContext_50_);
lean_ctor_set(v___x_57_, 11, v_currMacroScope_51_);
lean_ctor_set(v___x_57_, 12, v_cancelTk_x3f_53_);
lean_ctor_set(v___x_57_, 13, v_inheritedTraceOptions_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*14, v_diag_52_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*14 + 1, v_suppressElabErrors_54_);
v___x_58_ = l_Lean_Elab_Do_elabDoElem(v___x_29_, v_dec_30_, v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___x_57_, v___y_38_);
lean_dec_ref(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v___x_59_, lean_object* v_dec_60_, lean_object* v___x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v___x_10134__boxed_70_; lean_object* v_res_71_; 
v___x_10134__boxed_70_ = lean_unbox(v___x_61_);
v_res_71_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v___x_59_, v_dec_60_, v___x_10134__boxed_70_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_x_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
lean_inc_ref(v___y_73_);
v___x_81_ = lean_apply_8(v_x_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec_ref(v___y_83_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* v___y_92_, lean_object* v_mkInfoTree_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v_a_99_, lean_object* v_a_x3f_100_){
_start:
{
lean_object* v___x_102_; lean_object* v_infoState_103_; lean_object* v_trees_104_; lean_object* v___x_105_; 
v___x_102_ = lean_st_ref_get(v___y_92_);
v_infoState_103_ = lean_ctor_get(v___x_102_, 7);
lean_inc_ref(v_infoState_103_);
lean_dec(v___x_102_);
v_trees_104_ = lean_ctor_get(v_infoState_103_, 2);
lean_inc_ref(v_trees_104_);
lean_dec_ref(v_infoState_103_);
lean_inc(v___y_92_);
lean_inc_ref(v___y_98_);
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
v___x_105_ = lean_apply_8(v_mkInfoTree_93_, v_trees_104_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_92_, lean_box(0));
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_144_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_144_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_144_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_144_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v_infoState_111_; lean_object* v_env_112_; lean_object* v_nextMacroScope_113_; lean_object* v_ngen_114_; lean_object* v_auxDeclNGen_115_; lean_object* v_traceState_116_; lean_object* v_cache_117_; lean_object* v_messages_118_; lean_object* v_snapshotTasks_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v___x_110_ = lean_st_ref_take(v___y_92_);
v_infoState_111_ = lean_ctor_get(v___x_110_, 7);
v_env_112_ = lean_ctor_get(v___x_110_, 0);
v_nextMacroScope_113_ = lean_ctor_get(v___x_110_, 1);
v_ngen_114_ = lean_ctor_get(v___x_110_, 2);
v_auxDeclNGen_115_ = lean_ctor_get(v___x_110_, 3);
v_traceState_116_ = lean_ctor_get(v___x_110_, 4);
v_cache_117_ = lean_ctor_get(v___x_110_, 5);
v_messages_118_ = lean_ctor_get(v___x_110_, 6);
v_snapshotTasks_119_ = lean_ctor_get(v___x_110_, 8);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v___x_110_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snapshotTasks_119_);
lean_inc(v_infoState_111_);
lean_inc(v_messages_118_);
lean_inc(v_cache_117_);
lean_inc(v_traceState_116_);
lean_inc(v_auxDeclNGen_115_);
lean_inc(v_ngen_114_);
lean_inc(v_nextMacroScope_113_);
lean_inc(v_env_112_);
lean_dec(v___x_110_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v_enabled_123_; lean_object* v_assignment_124_; lean_object* v_lazyAssignment_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_141_; 
v_enabled_123_ = lean_ctor_get_uint8(v_infoState_111_, sizeof(void*)*3);
v_assignment_124_ = lean_ctor_get(v_infoState_111_, 0);
v_lazyAssignment_125_ = lean_ctor_get(v_infoState_111_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_infoState_111_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_infoState_111_, 2);
lean_dec(v_unused_142_);
v___x_127_ = v_infoState_111_;
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_lazyAssignment_125_);
lean_inc(v_assignment_124_);
lean_dec(v_infoState_111_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = l_Lean_PersistentArray_push___redArg(v_a_99_, v_a_106_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 2, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_assignment_124_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_lazyAssignment_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v___x_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_140_, sizeof(void*)*3, v_enabled_123_);
v___x_131_ = v_reuseFailAlloc_140_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 7, v___x_131_);
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_env_112_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_nextMacroScope_113_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_ngen_114_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_auxDeclNGen_115_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_traceState_116_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_cache_117_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_messages_118_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v_snapshotTasks_119_);
v___x_133_ = v_reuseFailAlloc_139_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = lean_st_ref_set(v___y_92_, v___x_133_);
v___x_135_ = lean_box(0);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_135_);
v___x_137_ = v___x_108_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_a_99_);
v_a_145_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_105_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_105_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_153_, lean_object* v_mkInfoTree_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v_a_160_, lean_object* v_a_x3f_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_153_, v_mkInfoTree_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v_a_160_, v_a_x3f_161_);
lean_dec(v_a_x3f_161_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_153_);
return v_res_163_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_unsigned_to_nat(32u);
v___x_165_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_167_ = ((size_t)5ULL);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_unsigned_to_nat(32u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_172_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_168_);
lean_ctor_set(v___x_172_, 3, v___x_168_);
lean_ctor_set_usize(v___x_172_, 4, v___x_167_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_infoState_176_; lean_object* v_trees_177_; lean_object* v___x_178_; lean_object* v_infoState_179_; lean_object* v_env_180_; lean_object* v_nextMacroScope_181_; lean_object* v_ngen_182_; lean_object* v_auxDeclNGen_183_; lean_object* v_traceState_184_; lean_object* v_cache_185_; lean_object* v_messages_186_; lean_object* v_snapshotTasks_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_208_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_infoState_176_ = lean_ctor_get(v___x_175_, 7);
lean_inc_ref(v_infoState_176_);
lean_dec(v___x_175_);
v_trees_177_ = lean_ctor_get(v_infoState_176_, 2);
lean_inc_ref(v_trees_177_);
lean_dec_ref(v_infoState_176_);
v___x_178_ = lean_st_ref_take(v___y_173_);
v_infoState_179_ = lean_ctor_get(v___x_178_, 7);
v_env_180_ = lean_ctor_get(v___x_178_, 0);
v_nextMacroScope_181_ = lean_ctor_get(v___x_178_, 1);
v_ngen_182_ = lean_ctor_get(v___x_178_, 2);
v_auxDeclNGen_183_ = lean_ctor_get(v___x_178_, 3);
v_traceState_184_ = lean_ctor_get(v___x_178_, 4);
v_cache_185_ = lean_ctor_get(v___x_178_, 5);
v_messages_186_ = lean_ctor_get(v___x_178_, 6);
v_snapshotTasks_187_ = lean_ctor_get(v___x_178_, 8);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_208_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_208_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snapshotTasks_187_);
lean_inc(v_infoState_179_);
lean_inc(v_messages_186_);
lean_inc(v_cache_185_);
lean_inc(v_traceState_184_);
lean_inc(v_auxDeclNGen_183_);
lean_inc(v_ngen_182_);
lean_inc(v_nextMacroScope_181_);
lean_inc(v_env_180_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_208_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
uint8_t v_enabled_191_; lean_object* v_assignment_192_; lean_object* v_lazyAssignment_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_206_; 
v_enabled_191_ = lean_ctor_get_uint8(v_infoState_179_, sizeof(void*)*3);
v_assignment_192_ = lean_ctor_get(v_infoState_179_, 0);
v_lazyAssignment_193_ = lean_ctor_get(v_infoState_179_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_infoState_179_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_infoState_179_, 2);
lean_dec(v_unused_207_);
v___x_195_ = v_infoState_179_;
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_lazyAssignment_193_);
lean_inc(v_assignment_192_);
lean_dec(v_infoState_179_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 2, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_assignment_192_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_lazyAssignment_193_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___x_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*3, v_enabled_191_);
v___x_199_ = v_reuseFailAlloc_205_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 7, v___x_199_);
v___x_201_ = v___x_189_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_env_180_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_nextMacroScope_181_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_ngen_182_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_auxDeclNGen_183_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_traceState_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 5, v_cache_185_);
lean_ctor_set(v_reuseFailAlloc_204_, 6, v_messages_186_);
lean_ctor_set(v_reuseFailAlloc_204_, 7, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_204_, 8, v_snapshotTasks_187_);
v___x_201_ = v_reuseFailAlloc_204_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_st_ref_set(v___y_173_, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_trees_177_);
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_209_);
lean_dec(v___y_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object* v_x_212_, lean_object* v_mkInfoTree_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_infoState_222_; uint8_t v_enabled_223_; 
v___x_221_ = lean_st_ref_get(v___y_219_);
v_infoState_222_ = lean_ctor_get(v___x_221_, 7);
lean_inc_ref(v_infoState_222_);
lean_dec(v___x_221_);
v_enabled_223_ = lean_ctor_get_uint8(v_infoState_222_, sizeof(void*)*3);
lean_dec_ref(v_infoState_222_);
if (v_enabled_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v_mkInfoTree_213_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
v___x_224_ = lean_apply_7(v_x_212_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, lean_box(0));
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v_r_227_; 
v___x_225_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_219_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
v_r_227_ = lean_apply_7(v_x_212_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, lean_box(0));
if (lean_obj_tag(v_r_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_252_; 
v_a_228_ = lean_ctor_get(v_r_227_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_r_227_);
if (v_isSharedCheck_252_ == 0)
{
v___x_230_ = v_r_227_;
v_isShared_231_ = v_isSharedCheck_252_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v_r_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_252_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
lean_inc(v_a_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_251_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_219_, v_mkInfoTree_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v_a_226_, v___x_233_);
lean_dec_ref(v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v___x_234_, 0);
lean_dec(v_unused_242_);
v___x_236_ = v___x_234_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_234_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_a_228_);
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_228_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_228_);
v_a_243_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_234_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_234_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_a_253_ = lean_ctor_get(v_r_227_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v_r_227_);
v___x_254_ = lean_box(0);
v___x_255_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_219_, v_mkInfoTree_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v_a_226_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_263_);
v___x_257_ = v___x_255_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_dec(v___x_255_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v_a_253_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_253_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_253_);
v_a_264_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_272_, lean_object* v_mkInfoTree_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_272_, v_mkInfoTree_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object* v_stx_282_, lean_object* v_output_283_, lean_object* v_trees_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_lctx_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_lctx_292_ = lean_ctor_get(v___y_287_, 2);
lean_inc_ref(v_lctx_292_);
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v_lctx_292_);
lean_ctor_set(v___x_293_, 1, v_stx_282_);
lean_ctor_set(v___x_293_, 2, v_output_283_);
v___x_294_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_trees_284_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_stx_297_, lean_object* v_output_298_, lean_object* v_trees_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_297_, v_output_298_, v_trees_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object* v_stx_308_, lean_object* v_output_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___f_318_; lean_object* v___x_319_; 
v___f_318_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_318_, 0, v_stx_308_);
lean_closure_set(v___f_318_, 1, v_output_309_);
v___x_319_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_310_, v___f_318_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object* v_stx_320_, lean_object* v_output_321_, lean_object* v_x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_320_, v_output_321_, v_x_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_beforeStx_331_, lean_object* v_afterStx_332_, lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_inc_ref(v___y_334_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_342_, 0, v_x_333_);
lean_closure_set(v___f_342_, 1, v___y_334_);
lean_inc(v_afterStx_332_);
lean_inc(v_beforeStx_331_);
v___x_343_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_343_, 0, lean_box(0));
lean_closure_set(v___x_343_, 1, v_beforeStx_331_);
lean_closure_set(v___x_343_, 2, v_afterStx_332_);
lean_closure_set(v___x_343_, 3, v___f_342_);
v___x_344_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_331_, v_afterStx_332_, v___x_343_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_beforeStx_353_, lean_object* v_afterStx_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_353_, v_afterStx_354_, v_x_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__12(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Array_mkArray0(lean_box(0));
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__18(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_401_ = l_String_toRawSubstring_x27(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_423_, lean_object* v_dec_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_423_);
v___x_434_ = l_Lean_Syntax_isOfKind(v_stx_423_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec_ref(v_dec_424_);
lean_dec(v_stx_423_);
v___x_435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_435_;
}
else
{
lean_object* v_ref_436_; lean_object* v_quotContext_437_; lean_object* v_currMacroScope_438_; lean_object* v___x_439_; lean_object* v_tk_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___f_470_; lean_object* v___x_471_; 
v_ref_436_ = lean_ctor_get(v_a_430_, 5);
v_quotContext_437_ = lean_ctor_get(v_a_430_, 10);
v_currMacroScope_438_ = lean_ctor_get(v_a_430_, 11);
v___x_439_ = lean_unsigned_to_nat(0u);
v_tk_440_ = l_Lean_Syntax_getArg(v_stx_423_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = l_Lean_Syntax_getArg(v_stx_423_, v___x_441_);
v___x_443_ = 0;
v___x_444_ = l_Lean_SourceInfo_fromRef(v_ref_436_, v___x_443_);
v___x_445_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__6));
v___x_446_ = l_Lean_SourceInfo_fromRef(v_tk_440_, v___x_434_);
lean_dec(v_tk_440_);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_450_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_451_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__12, &l_Lean_Elab_Do_elabDoRepeat___closed__12_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__12);
lean_inc_n(v___x_444_, 8);
v___x_452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_452_, 0, v___x_444_);
lean_ctor_set(v___x_452_, 1, v___x_449_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
v___x_453_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_454_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__15));
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_444_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_Syntax_node1(v___x_444_, v___x_453_, v___x_455_);
v___x_457_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_444_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__18, &l_Lean_Elab_Do_elabDoRepeat___closed__18_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__18);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
lean_inc(v_currMacroScope_438_);
lean_inc(v_quotContext_437_);
v___x_461_ = l_Lean_addMacroScope(v_quotContext_437_, v___x_460_, v_currMacroScope_438_);
v___x_462_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__26));
v___x_463_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_463_, 0, v___x_444_);
lean_ctor_set(v___x_463_, 1, v___x_459_);
lean_ctor_set(v___x_463_, 2, v___x_461_);
lean_ctor_set(v___x_463_, 3, v___x_462_);
v___x_464_ = l_Lean_Syntax_node4(v___x_444_, v___x_450_, v___x_452_, v___x_456_, v___x_458_, v___x_463_);
v___x_465_ = l_Lean_Syntax_node1(v___x_444_, v___x_449_, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__27));
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_444_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Syntax_node4(v___x_444_, v___x_445_, v___x_448_, v___x_465_, v___x_467_, v___x_442_);
v___x_469_ = lean_box(v___x_434_);
lean_inc(v___x_468_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_470_, 0, v___x_468_);
lean_closure_set(v___f_470_, 1, v_dec_424_);
lean_closure_set(v___f_470_, 2, v___x_469_);
v___x_471_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_423_, v___x_468_, v___f_470_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_472_, lean_object* v_dec_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_472_, v_dec_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_483_, lean_object* v_beforeStx_484_, lean_object* v_afterStx_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_484_, v_afterStx_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_496_, lean_object* v_beforeStx_497_, lean_object* v_afterStx_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_496_, v_beforeStx_497_, v_afterStx_498_, v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_509_, lean_object* v_stx_510_, lean_object* v_output_511_, lean_object* v_x_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_510_, v_output_511_, v_x_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_521_, lean_object* v_stx_522_, lean_object* v_output_523_, lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_521_, v_stx_522_, v_output_523_, v_x_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_549_, lean_object* v_x_550_, lean_object* v_mkInfoTree_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_550_, v_mkInfoTree_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_560_, lean_object* v_x_561_, lean_object* v_mkInfoTree_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_560_, v_x_561_, v_mkInfoTree_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_580_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_581_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_583_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_584_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_580_, v___x_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_591_ = l_Lean_addBuiltinDocString(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhileH(lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__1));
lean_inc(v_x_636_);
v___x_640_ = l_Lean_Syntax_isOfKind(v_x_636_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_x_636_);
v___x_641_ = l_Lean_Macro_throwUnsupported___redArg(v_a_638_);
return v___x_641_;
}
else
{
lean_object* v_ref_642_; lean_object* v___x_643_; lean_object* v_tk_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_ref_642_ = lean_ctor_get(v_a_637_, 5);
v___x_643_ = lean_unsigned_to_nat(0u);
v_tk_644_ = l_Lean_Syntax_getArg(v_x_636_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = l_Lean_Syntax_getArg(v_x_636_, v___x_645_);
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = l_Lean_Syntax_getArg(v_x_636_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(5u);
v___x_650_ = l_Lean_Syntax_getArg(v_x_636_, v___x_649_);
lean_dec(v_x_636_);
v___x_651_ = 0;
v___x_652_ = l_Lean_SourceInfo_fromRef(v_ref_642_, v___x_651_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_654_ = l_Lean_SourceInfo_fromRef(v_tk_644_, v___x_640_);
lean_dec(v_tk_644_);
v___x_655_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__2));
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__4));
v___x_658_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_659_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__6));
v___x_660_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__8));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__9));
lean_inc_n(v___x_652_, 17);
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_652_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__11));
v___x_664_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__12));
v___x_665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_652_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_Syntax_node2(v___x_652_, v___x_658_, v___x_646_, v___x_665_);
v___x_667_ = l_Lean_Syntax_node2(v___x_652_, v___x_663_, v___x_666_, v___x_648_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__13));
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_652_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__12, &l_Lean_Elab_Do_elabDoRepeat___closed__12_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__12);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_652_);
lean_ctor_set(v___x_671_, 1, v___x_658_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__14));
v___x_673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_652_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__16));
v___x_675_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__17));
v___x_676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_652_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Lean_Syntax_node1(v___x_652_, v___x_674_, v___x_676_);
lean_inc_ref_n(v___x_671_, 2);
v___x_678_ = l_Lean_Syntax_node2(v___x_652_, v___x_659_, v___x_677_, v___x_671_);
v___x_679_ = l_Lean_Syntax_node1(v___x_652_, v___x_658_, v___x_678_);
v___x_680_ = l_Lean_Syntax_node1(v___x_652_, v___x_657_, v___x_679_);
v___x_681_ = l_Lean_Syntax_node2(v___x_652_, v___x_658_, v___x_673_, v___x_680_);
v___x_682_ = l_Lean_Syntax_node6(v___x_652_, v___x_660_, v___x_662_, v___x_667_, v___x_669_, v___x_650_, v___x_671_, v___x_681_);
v___x_683_ = l_Lean_Syntax_node2(v___x_652_, v___x_659_, v___x_682_, v___x_671_);
v___x_684_ = l_Lean_Syntax_node1(v___x_652_, v___x_658_, v___x_683_);
v___x_685_ = l_Lean_Syntax_node1(v___x_652_, v___x_657_, v___x_684_);
v___x_686_ = l_Lean_Syntax_node2(v___x_652_, v___x_653_, v___x_656_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_a_638_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhileH___boxed(lean_object* v_x_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Elab_Do_expandDoWhileH(v_x_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1(){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_699_ = l_Lean_Elab_macroAttribute;
v___x_700_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__1));
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___closed__1));
v___x_702_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhileH___boxed), 3, 0);
v___x_703_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_699_, v___x_700_, v___x_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1___boxed(lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1();
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_712_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_x_712_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec(v_x_712_);
v___x_717_ = l_Lean_Macro_throwUnsupported___redArg(v_a_714_);
return v___x_717_;
}
else
{
lean_object* v_ref_718_; lean_object* v___x_719_; lean_object* v_tk_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_ref_718_ = lean_ctor_get(v_a_713_, 5);
v___x_719_ = lean_unsigned_to_nat(0u);
v_tk_720_ = l_Lean_Syntax_getArg(v_x_712_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = l_Lean_Syntax_getArg(v_x_712_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = l_Lean_Syntax_getArg(v_x_712_, v___x_723_);
lean_dec(v_x_712_);
v___x_725_ = 0;
v___x_726_ = l_Lean_SourceInfo_fromRef(v_ref_718_, v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_728_ = l_Lean_SourceInfo_fromRef(v_tk_720_, v___x_716_);
lean_dec(v_tk_720_);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__2));
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__4));
v___x_732_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_733_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__6));
v___x_734_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__8));
v___x_735_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__9));
lean_inc_n(v___x_726_, 15);
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_726_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__11));
v___x_738_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__12, &l_Lean_Elab_Do_elabDoRepeat___closed__12_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__12);
v___x_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_739_, 0, v___x_726_);
lean_ctor_set(v___x_739_, 1, v___x_732_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
lean_inc_ref_n(v___x_739_, 3);
v___x_740_ = l_Lean_Syntax_node2(v___x_726_, v___x_737_, v___x_739_, v___x_722_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__13));
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_726_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__14));
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_726_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__16));
v___x_746_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__17));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_726_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_Syntax_node1(v___x_726_, v___x_745_, v___x_747_);
v___x_749_ = l_Lean_Syntax_node2(v___x_726_, v___x_733_, v___x_748_, v___x_739_);
v___x_750_ = l_Lean_Syntax_node1(v___x_726_, v___x_732_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___x_726_, v___x_731_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node2(v___x_726_, v___x_732_, v___x_744_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node6(v___x_726_, v___x_734_, v___x_736_, v___x_740_, v___x_742_, v___x_724_, v___x_739_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node2(v___x_726_, v___x_733_, v___x_753_, v___x_739_);
v___x_755_ = l_Lean_Syntax_node1(v___x_726_, v___x_732_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node1(v___x_726_, v___x_731_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node2(v___x_726_, v___x_727_, v___x_730_, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_a_714_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Elab_Do_expandDoWhile(v_x_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_770_ = l_Lean_Elab_macroAttribute;
v___x_771_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_773_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_774_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_770_, v___x_771_, v___x_772_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
lean_inc(v_x_790_);
v___x_794_ = l_Lean_Syntax_isOfKind(v_x_790_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_x_790_);
v___x_795_ = l_Lean_Macro_throwUnsupported___redArg(v_a_792_);
return v___x_795_;
}
else
{
lean_object* v_ref_796_; lean_object* v___x_797_; lean_object* v_tk_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_ref_796_ = lean_ctor_get(v_a_791_, 5);
v___x_797_ = lean_unsigned_to_nat(0u);
v_tk_798_ = l_Lean_Syntax_getArg(v_x_790_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = l_Lean_Syntax_getArg(v_x_790_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = l_Lean_Syntax_getArg(v_x_790_, v___x_801_);
lean_dec(v_x_790_);
v___x_803_ = 0;
v___x_804_ = l_Lean_SourceInfo_fromRef(v_ref_796_, v___x_803_);
v___x_805_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_806_ = l_Lean_SourceInfo_fromRef(v_tk_798_, v___x_794_);
lean_dec(v_tk_798_);
v___x_807_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__2));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__4));
v___x_810_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_811_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__6));
v___x_812_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_813_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__27));
lean_inc_n(v___x_804_, 18);
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_804_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_Syntax_node2(v___x_804_, v___x_812_, v___x_814_, v___x_800_);
v___x_816_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__4));
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_804_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Syntax_node1(v___x_804_, v___x_810_, v___x_817_);
v___x_819_ = l_Lean_Syntax_node2(v___x_804_, v___x_811_, v___x_815_, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__8));
v___x_821_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__9));
v___x_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__11));
v___x_824_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__12, &l_Lean_Elab_Do_elabDoRepeat___closed__12_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__12);
v___x_825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_825_, 0, v___x_804_);
lean_ctor_set(v___x_825_, 1, v___x_810_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
lean_inc_ref_n(v___x_825_, 4);
v___x_826_ = l_Lean_Syntax_node2(v___x_804_, v___x_823_, v___x_825_, v___x_802_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__13));
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_804_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__16));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhileH___closed__17));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_804_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_Syntax_node1(v___x_804_, v___x_829_, v___x_831_);
v___x_833_ = l_Lean_Syntax_node2(v___x_804_, v___x_811_, v___x_832_, v___x_825_);
v___x_834_ = l_Lean_Syntax_node1(v___x_804_, v___x_810_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node1(v___x_804_, v___x_809_, v___x_834_);
v___x_836_ = l_Lean_Syntax_node6(v___x_804_, v___x_820_, v___x_822_, v___x_826_, v___x_828_, v___x_835_, v___x_825_, v___x_825_);
v___x_837_ = l_Lean_Syntax_node2(v___x_804_, v___x_811_, v___x_836_, v___x_825_);
v___x_838_ = l_Lean_Syntax_node2(v___x_804_, v___x_810_, v___x_819_, v___x_837_);
v___x_839_ = l_Lean_Syntax_node1(v___x_804_, v___x_809_, v___x_838_);
v___x_840_ = l_Lean_Syntax_node2(v___x_804_, v___x_805_, v___x_808_, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_a_792_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_842_, v_a_843_, v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = l_Lean_Elab_macroAttribute;
v___x_854_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_856_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_857_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_853_, v___x_854_, v___x_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_859_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhileH___regBuiltin_Lean_Elab_Do_expandDoWhileH__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
