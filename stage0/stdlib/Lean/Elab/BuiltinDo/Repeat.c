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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnit___redArg(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__6_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__10_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__13_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unreachable"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__15_value),LEAN_SCALAR_PTR_LITERAL(90, 182, 141, 4, 195, 151, 157, 51)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unreachable!"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__17_value;
static const lean_array_object l_Lean_Elab_Do_elabDoRepeat___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__19_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__20_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__22_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__23 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__24 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__24_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__25 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoRepeat___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__26;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__27 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__28_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__27_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__28 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__28_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__29 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__30 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__30_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Loop.mk"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__31 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__31_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoRepeat___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__32;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Loop"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__33 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__34 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__33_value),LEAN_SCALAR_PTR_LITERAL(77, 134, 225, 236, 222, 42, 27, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__34_value),LEAN_SCALAR_PTR_LITERAL(121, 43, 2, 225, 80, 67, 164, 196)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__35 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__33_value),LEAN_SCALAR_PTR_LITERAL(244, 180, 170, 243, 159, 48, 205, 98)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__34_value),LEAN_SCALAR_PTR_LITERAL(92, 204, 229, 77, 211, 121, 59, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__36 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__37 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__36_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__38 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__39 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__37_value),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__39_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__40 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__40_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__41 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__41_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__42 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__42_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__43 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__43_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__44 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__44_value;
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 607, .m_capacity = 607, .m_length = 604, .m_data = "Builtin do-element elaborator for `repeat` (syntax kind `Lean.Parser.Term.doRepeat`).\n\nExpands to `for _ in Loop.mk do ...`. When the body cannot `break`, the loop's own expression\ntype is fixed to `PUnit`, yet the surrounding do block may require a different result type;\nwe append an `unreachable!` so the continuation has a polymorphic value of any type. The\n`unreachable!` is never actually executed (the loop never terminates normally), and any\ndead-code warning that fires on the surrounding continuation is actionable — the user can\nremove the following code without breaking the do block's type.\n"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doWhile"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 22, 162, 157, 218, 80, 50, 216)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoWhile___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__7_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_expandDoWhile___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Lean_Elab_Do_expandDoWhile___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoWhile___closed__10_value;
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
static const lean_string_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doRepeatUntil"};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__2_value),LEAN_SCALAR_PTR_LITERAL(46, 11, 184, 16, 157, 182, 78, 231)}};
static const lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoRepeatUntil___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object* v_expanded_29_, lean_object* v_dec_30_, uint8_t v___x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_toCold_40_; lean_object* v_currRecDepth_41_; lean_object* v_ref_42_; uint8_t v_diag_43_; uint8_t v_suppressElabErrors_44_; lean_object* v_ref_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_toCold_40_ = lean_ctor_get(v___y_37_, 0);
v_currRecDepth_41_ = lean_ctor_get(v___y_37_, 1);
v_ref_42_ = lean_ctor_get(v___y_37_, 2);
v_diag_43_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*3);
v_suppressElabErrors_44_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*3 + 1);
v_ref_45_ = l_Lean_replaceRef(v_expanded_29_, v_ref_42_);
lean_inc(v_currRecDepth_41_);
lean_inc_ref(v_toCold_40_);
v___x_46_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_46_, 0, v_toCold_40_);
lean_ctor_set(v___x_46_, 1, v_currRecDepth_41_);
lean_ctor_set(v___x_46_, 2, v_ref_45_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*3, v_diag_43_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*3 + 1, v_suppressElabErrors_44_);
v___x_47_ = l_Lean_Elab_Do_elabDoElem(v_expanded_29_, v_dec_30_, v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___x_46_, v___y_38_);
lean_dec_ref_known(v___x_46_, 3);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v_expanded_48_, lean_object* v_dec_49_, lean_object* v___x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v___x_14719__boxed_59_; lean_object* v_res_60_; 
v___x_14719__boxed_59_ = lean_unbox(v___x_50_);
v_res_60_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_48_, v_dec_49_, v___x_14719__boxed_59_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
lean_inc_ref(v___y_62_);
v___x_70_ = lean_apply_8(v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec_ref(v___y_72_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* v___y_81_, lean_object* v_mkInfoTree_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v_a_88_, lean_object* v_a_x3f_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_infoState_92_; lean_object* v_trees_93_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_get(v___y_81_);
v_infoState_92_ = lean_ctor_get(v___x_91_, 7);
lean_inc_ref(v_infoState_92_);
lean_dec(v___x_91_);
v_trees_93_ = lean_ctor_get(v_infoState_92_, 2);
lean_inc_ref(v_trees_93_);
lean_dec_ref(v_infoState_92_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
v___x_94_ = lean_apply_8(v_mkInfoTree_82_, v_trees_93_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_81_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_133_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_133_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_133_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_133_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v_infoState_100_; lean_object* v_env_101_; lean_object* v_nextMacroScope_102_; lean_object* v_ngen_103_; lean_object* v_auxDeclNGen_104_; lean_object* v_traceState_105_; lean_object* v_cache_106_; lean_object* v_messages_107_; lean_object* v_snapshotTasks_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_132_; 
v___x_99_ = lean_st_ref_take(v___y_81_);
v_infoState_100_ = lean_ctor_get(v___x_99_, 7);
v_env_101_ = lean_ctor_get(v___x_99_, 0);
v_nextMacroScope_102_ = lean_ctor_get(v___x_99_, 1);
v_ngen_103_ = lean_ctor_get(v___x_99_, 2);
v_auxDeclNGen_104_ = lean_ctor_get(v___x_99_, 3);
v_traceState_105_ = lean_ctor_get(v___x_99_, 4);
v_cache_106_ = lean_ctor_get(v___x_99_, 5);
v_messages_107_ = lean_ctor_get(v___x_99_, 6);
v_snapshotTasks_108_ = lean_ctor_get(v___x_99_, 8);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_132_ == 0)
{
v___x_110_ = v___x_99_;
v_isShared_111_ = v_isSharedCheck_132_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_snapshotTasks_108_);
lean_inc(v_infoState_100_);
lean_inc(v_messages_107_);
lean_inc(v_cache_106_);
lean_inc(v_traceState_105_);
lean_inc(v_auxDeclNGen_104_);
lean_inc(v_ngen_103_);
lean_inc(v_nextMacroScope_102_);
lean_inc(v_env_101_);
lean_dec(v___x_99_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_132_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
uint8_t v_enabled_112_; lean_object* v_assignment_113_; lean_object* v_lazyAssignment_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_enabled_112_ = lean_ctor_get_uint8(v_infoState_100_, sizeof(void*)*3);
v_assignment_113_ = lean_ctor_get(v_infoState_100_, 0);
v_lazyAssignment_114_ = lean_ctor_get(v_infoState_100_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_infoState_100_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v_infoState_100_, 2);
lean_dec(v_unused_131_);
v___x_116_ = v_infoState_100_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_lazyAssignment_114_);
lean_inc(v_assignment_113_);
lean_dec(v_infoState_100_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = l_Lean_PersistentArray_push___redArg(v_a_88_, v_a_95_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 2, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_assignment_113_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_lazyAssignment_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v___x_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_129_, sizeof(void*)*3, v_enabled_112_);
v___x_120_ = v_reuseFailAlloc_129_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 7, v___x_120_);
v___x_122_ = v___x_110_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_env_101_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_nextMacroScope_102_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_ngen_103_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_auxDeclNGen_104_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_traceState_105_);
lean_ctor_set(v_reuseFailAlloc_128_, 5, v_cache_106_);
lean_ctor_set(v_reuseFailAlloc_128_, 6, v_messages_107_);
lean_ctor_set(v_reuseFailAlloc_128_, 7, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_128_, 8, v_snapshotTasks_108_);
v___x_122_ = v_reuseFailAlloc_128_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = lean_st_ref_put(v___y_81_, v___x_122_);
v___x_124_ = lean_box(0);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_124_);
v___x_126_ = v___x_97_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec_ref(v_a_88_);
v_a_134_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_94_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_94_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_142_, lean_object* v_mkInfoTree_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v_a_149_, lean_object* v_a_x3f_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_142_, v_mkInfoTree_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v_a_149_, v_a_x3f_150_);
lean_dec(v_a_x3f_150_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_142_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(32u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((size_t)5ULL);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_161_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_157_);
lean_ctor_set(v___x_161_, 3, v___x_157_);
lean_ctor_set_usize(v___x_161_, 4, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_infoState_165_; lean_object* v_trees_166_; lean_object* v___x_167_; lean_object* v_infoState_168_; lean_object* v_env_169_; lean_object* v_nextMacroScope_170_; lean_object* v_ngen_171_; lean_object* v_auxDeclNGen_172_; lean_object* v_traceState_173_; lean_object* v_cache_174_; lean_object* v_messages_175_; lean_object* v_snapshotTasks_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_197_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_infoState_165_ = lean_ctor_get(v___x_164_, 7);
lean_inc_ref(v_infoState_165_);
lean_dec(v___x_164_);
v_trees_166_ = lean_ctor_get(v_infoState_165_, 2);
lean_inc_ref(v_trees_166_);
lean_dec_ref(v_infoState_165_);
v___x_167_ = lean_st_ref_take(v___y_162_);
v_infoState_168_ = lean_ctor_get(v___x_167_, 7);
v_env_169_ = lean_ctor_get(v___x_167_, 0);
v_nextMacroScope_170_ = lean_ctor_get(v___x_167_, 1);
v_ngen_171_ = lean_ctor_get(v___x_167_, 2);
v_auxDeclNGen_172_ = lean_ctor_get(v___x_167_, 3);
v_traceState_173_ = lean_ctor_get(v___x_167_, 4);
v_cache_174_ = lean_ctor_get(v___x_167_, 5);
v_messages_175_ = lean_ctor_get(v___x_167_, 6);
v_snapshotTasks_176_ = lean_ctor_get(v___x_167_, 8);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_197_ == 0)
{
v___x_178_ = v___x_167_;
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snapshotTasks_176_);
lean_inc(v_infoState_168_);
lean_inc(v_messages_175_);
lean_inc(v_cache_174_);
lean_inc(v_traceState_173_);
lean_inc(v_auxDeclNGen_172_);
lean_inc(v_ngen_171_);
lean_inc(v_nextMacroScope_170_);
lean_inc(v_env_169_);
lean_dec(v___x_167_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v_enabled_180_; lean_object* v_assignment_181_; lean_object* v_lazyAssignment_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_enabled_180_ = lean_ctor_get_uint8(v_infoState_168_, sizeof(void*)*3);
v_assignment_181_ = lean_ctor_get(v_infoState_168_, 0);
v_lazyAssignment_182_ = lean_ctor_get(v_infoState_168_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_infoState_168_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_infoState_168_, 2);
lean_dec(v_unused_196_);
v___x_184_ = v_infoState_168_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_lazyAssignment_182_);
lean_inc(v_assignment_181_);
lean_dec(v_infoState_168_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 2, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_assignment_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_lazyAssignment_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___x_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*3, v_enabled_180_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 7, v___x_188_);
v___x_190_ = v___x_178_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_env_169_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_nextMacroScope_170_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_ngen_171_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_auxDeclNGen_172_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_traceState_173_);
lean_ctor_set(v_reuseFailAlloc_193_, 5, v_cache_174_);
lean_ctor_set(v_reuseFailAlloc_193_, 6, v_messages_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 7, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 8, v_snapshotTasks_176_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_st_ref_put(v___y_162_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_trees_166_);
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_198_);
lean_dec(v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object* v_x_201_, lean_object* v_mkInfoTree_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_infoState_211_; uint8_t v_enabled_212_; 
v___x_210_ = lean_st_ref_get(v___y_208_);
v_infoState_211_ = lean_ctor_get(v___x_210_, 7);
lean_inc_ref(v_infoState_211_);
lean_dec(v___x_210_);
v_enabled_212_ = lean_ctor_get_uint8(v_infoState_211_, sizeof(void*)*3);
lean_dec_ref(v_infoState_211_);
if (v_enabled_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v_mkInfoTree_202_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
v___x_213_ = lean_apply_7(v_x_201_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, lean_box(0));
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v_r_216_; 
v___x_214_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_208_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_214_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
v_r_216_ = lean_apply_7(v_x_201_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, lean_box(0));
if (lean_obj_tag(v_r_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_241_; 
v_a_217_ = lean_ctor_get(v_r_216_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_r_216_);
if (v_isSharedCheck_241_ == 0)
{
v___x_219_ = v_r_216_;
v_isShared_220_ = v_isSharedCheck_241_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v_r_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_241_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
lean_inc(v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_240_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_208_, v_mkInfoTree_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v_a_215_, v___x_222_);
lean_dec_ref(v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v___x_223_, 0);
lean_dec(v_unused_231_);
v___x_225_ = v___x_223_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_dec(v___x_223_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v_a_217_);
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_217_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_217_);
v_a_232_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_223_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_223_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_242_ = lean_ctor_get(v_r_216_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v_r_216_, 1);
v___x_243_ = lean_box(0);
v___x_244_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_208_, v_mkInfoTree_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v_a_215_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v___x_244_, 0);
lean_dec(v_unused_252_);
v___x_246_ = v___x_244_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_dec(v___x_244_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 1);
lean_ctor_set(v___x_246_, 0, v_a_242_);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_242_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_242_);
v_a_253_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_244_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_244_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_261_, lean_object* v_mkInfoTree_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_261_, v_mkInfoTree_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object* v_stx_271_, lean_object* v_output_272_, lean_object* v_trees_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_lctx_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_lctx_281_ = lean_ctor_get(v___y_276_, 2);
lean_inc_ref(v_lctx_281_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_lctx_281_);
lean_ctor_set(v___x_282_, 1, v_stx_271_);
lean_ctor_set(v___x_282_, 2, v_output_272_);
v___x_283_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_trees_273_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_stx_286_, lean_object* v_output_287_, lean_object* v_trees_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_286_, v_output_287_, v_trees_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object* v_stx_297_, lean_object* v_output_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; 
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_307_, 0, v_stx_297_);
lean_closure_set(v___f_307_, 1, v_output_298_);
v___x_308_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_299_, v___f_307_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object* v_stx_309_, lean_object* v_output_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_309_, v_output_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_beforeStx_320_, lean_object* v_afterStx_321_, lean_object* v_x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_inc_ref(v___y_323_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_331_, 0, v_x_322_);
lean_closure_set(v___f_331_, 1, v___y_323_);
lean_inc(v_afterStx_321_);
lean_inc(v_beforeStx_320_);
v___x_332_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_332_, 0, lean_box(0));
lean_closure_set(v___x_332_, 1, v_beforeStx_320_);
lean_closure_set(v___x_332_, 2, v_afterStx_321_);
lean_closure_set(v___x_332_, 3, v___f_331_);
v___x_333_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_320_, v_afterStx_321_, v___x_332_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_333_) == 0)
{
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_beforeStx_342_, lean_object* v_afterStx_343_, lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_342_, v_afterStx_343_, v_x_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__26(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Array_mkArray0(lean_box(0));
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__32(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__31));
v___x_425_ = l_String_toRawSubstring_x27(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_458_, lean_object* v_dec_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; lean_object* v_expanded_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_458_);
v___x_469_ = l_Lean_Syntax_isOfKind(v_stx_458_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v___x_550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_tk_575_; lean_object* v___y_577_; lean_object* v_var_x3f_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___x_629_; lean_object* v_inv_x3f_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v_tk_575_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_551_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_649_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_629_);
v___x_650_ = l_Lean_Syntax_isNone(v___x_649_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
lean_inc(v___x_649_);
v___x_651_ = l_Lean_Syntax_matchesNull(v___x_649_, v___x_629_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_649_);
lean_dec(v_tk_575_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v___x_652_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_652_;
}
else
{
lean_object* v_inv_x3f_653_; 
v_inv_x3f_653_ = l_Lean_Syntax_getArg(v___x_649_, v___x_551_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_653_);
v___x_657_ = l_Lean_Syntax_isOfKind(v_inv_x3f_653_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v_inv_x3f_653_);
lean_dec(v_tk_575_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v___x_658_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_658_;
}
else
{
goto v___jp_654_;
}
}
else
{
goto v___jp_654_;
}
v___jp_654_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_inv_x3f_653_);
v_inv_x3f_631_ = v___x_655_;
v___y_632_ = v_a_460_;
v___y_633_ = v_a_461_;
v___y_634_ = v_a_462_;
v___y_635_ = v_a_463_;
v___y_636_ = v_a_464_;
v___y_637_ = v_a_465_;
v___y_638_ = v_a_466_;
goto v___jp_630_;
}
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v___x_649_);
v___x_659_ = lean_box(0);
v_inv_x3f_631_ = v___x_659_;
v___y_632_ = v_a_460_;
v___y_633_ = v_a_461_;
v___y_634_ = v_a_462_;
v___y_635_ = v_a_463_;
v___y_636_ = v_a_464_;
v___y_637_ = v_a_465_;
v___y_638_ = v_a_466_;
goto v___jp_630_;
}
v___jp_552_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_inc_ref(v___y_564_);
v___x_570_ = l_Array_append___redArg(v___y_564_, v___y_569_);
lean_dec_ref(v___y_569_);
lean_inc(v___y_560_);
lean_inc(v___y_565_);
v___x_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_571_, 0, v___y_565_);
lean_ctor_set(v___x_571_, 1, v___y_560_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
if (lean_obj_tag(v___y_555_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_573_; 
v_val_572_ = lean_ctor_get(v___y_555_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v___y_555_, 1);
v___x_573_ = l_Array_mkArray1___redArg(v_val_572_);
v___y_483_ = v___y_553_;
v___y_484_ = v___y_554_;
v___y_485_ = v___y_556_;
v___y_486_ = v___y_557_;
v___y_487_ = v___y_558_;
v___y_488_ = v___y_559_;
v___y_489_ = v___y_560_;
v___y_490_ = v___y_561_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___x_571_;
v___y_495_ = v___y_565_;
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___x_573_;
goto v___jp_482_;
}
else
{
lean_object* v___x_574_; 
lean_dec(v___y_555_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_483_ = v___y_553_;
v___y_484_ = v___y_554_;
v___y_485_ = v___y_556_;
v___y_486_ = v___y_557_;
v___y_487_ = v___y_558_;
v___y_488_ = v___y_559_;
v___y_489_ = v___y_560_;
v___y_490_ = v___y_561_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___x_571_;
v___y_495_ = v___y_565_;
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___x_574_;
goto v___jp_482_;
}
}
v___jp_576_:
{
lean_object* v_toCold_586_; lean_object* v_ref_587_; lean_object* v_quotContext_588_; lean_object* v_currMacroScope_589_; lean_object* v___x_590_; lean_object* v_seq_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toCold_586_ = lean_ctor_get(v___y_584_, 0);
v_ref_587_ = lean_ctor_get(v___y_584_, 2);
v_quotContext_588_ = lean_ctor_get(v_toCold_586_, 8);
v_currMacroScope_589_ = lean_ctor_get(v_toCold_586_, 9);
v___x_590_ = lean_unsigned_to_nat(3u);
v_seq_591_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_590_);
v___x_592_ = 0;
v___x_593_ = l_Lean_SourceInfo_fromRef(v_ref_587_, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__20));
v___x_595_ = l_Lean_SourceInfo_fromRef(v_tk_575_, v___x_469_);
lean_dec(v_tk_575_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_599_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__25));
v___x_600_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
lean_inc_n(v___x_593_, 7);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_593_);
lean_ctor_set(v___x_601_, 1, v___x_598_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__28));
v___x_603_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__29));
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_593_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_Syntax_node1(v___x_593_, v___x_602_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__30));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_593_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__32, &l_Lean_Elab_Do_elabDoRepeat___closed__32_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__32);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__35));
lean_inc(v_currMacroScope_589_);
lean_inc(v_quotContext_588_);
v___x_610_ = l_Lean_addMacroScope(v_quotContext_588_, v___x_609_, v_currMacroScope_589_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__40));
v___x_612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_612_, 0, v___x_593_);
lean_ctor_set(v___x_612_, 1, v___x_608_);
lean_ctor_set(v___x_612_, 2, v___x_610_);
lean_ctor_set(v___x_612_, 3, v___x_611_);
v___x_613_ = l_Lean_Syntax_node4(v___x_593_, v___x_599_, v___x_601_, v___x_605_, v___x_607_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node1(v___x_593_, v___x_598_, v___x_613_);
if (lean_obj_tag(v___y_577_) == 1)
{
lean_object* v_val_615_; lean_object* v___x_616_; 
v_val_615_ = lean_ctor_get(v___y_577_, 0);
lean_inc(v_val_615_);
lean_dec_ref_known(v___y_577_, 1);
v___x_616_ = l_Array_mkArray1___redArg(v_val_615_);
v___y_553_ = v___y_581_;
v___y_554_ = v___x_594_;
v___y_555_ = v_var_x3f_578_;
v___y_556_ = v_seq_591_;
v___y_557_ = v___y_584_;
v___y_558_ = v___y_585_;
v___y_559_ = v___y_579_;
v___y_560_ = v___x_598_;
v___y_561_ = v___y_582_;
v___y_562_ = v___x_614_;
v___y_563_ = v___x_597_;
v___y_564_ = v___x_600_;
v___y_565_ = v___x_593_;
v___y_566_ = v___y_583_;
v___y_567_ = v___y_580_;
v___y_568_ = v_ref_587_;
v___y_569_ = v___x_616_;
goto v___jp_552_;
}
else
{
lean_object* v___x_617_; 
lean_dec(v___y_577_);
v___x_617_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_553_ = v___y_581_;
v___y_554_ = v___x_594_;
v___y_555_ = v_var_x3f_578_;
v___y_556_ = v_seq_591_;
v___y_557_ = v___y_584_;
v___y_558_ = v___y_585_;
v___y_559_ = v___y_579_;
v___y_560_ = v___x_598_;
v___y_561_ = v___y_582_;
v___y_562_ = v___x_614_;
v___y_563_ = v___x_597_;
v___y_564_ = v___x_600_;
v___y_565_ = v___x_593_;
v___y_566_ = v___y_583_;
v___y_567_ = v___y_580_;
v___y_568_ = v_ref_587_;
v___y_569_ = v___x_617_;
goto v___jp_552_;
}
}
v___jp_618_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___y_623_);
v___y_577_ = v___y_622_;
v_var_x3f_578_ = v___x_628_;
v___y_579_ = v___y_625_;
v___y_580_ = v___y_621_;
v___y_581_ = v___y_626_;
v___y_582_ = v___y_619_;
v___y_583_ = v___y_620_;
v___y_584_ = v___y_627_;
v___y_585_ = v___y_624_;
goto v___jp_576_;
}
v___jp_630_:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(2u);
v___x_640_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_639_);
v___x_641_ = l_Lean_Syntax_isNone(v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; 
lean_inc(v___x_640_);
v___x_642_ = l_Lean_Syntax_matchesNull(v___x_640_, v___x_629_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_640_);
lean_dec(v_inv_x3f_631_);
lean_dec(v_tk_575_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v___x_643_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_643_;
}
else
{
lean_object* v_var_x3f_644_; 
v_var_x3f_644_ = l_Lean_Syntax_getArg(v___x_640_, v___x_551_);
lean_dec(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_var_x3f_644_);
v___x_646_ = l_Lean_Syntax_isOfKind(v_var_x3f_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v_var_x3f_644_);
lean_dec(v_inv_x3f_631_);
lean_dec(v_tk_575_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v___x_647_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_647_;
}
else
{
v___y_619_ = v___y_635_;
v___y_620_ = v___y_636_;
v___y_621_ = v___y_633_;
v___y_622_ = v_inv_x3f_631_;
v___y_623_ = v_var_x3f_644_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_634_;
v___y_627_ = v___y_637_;
goto v___jp_618_;
}
}
else
{
v___y_619_ = v___y_635_;
v___y_620_ = v___y_636_;
v___y_621_ = v___y_633_;
v___y_622_ = v_inv_x3f_631_;
v___y_623_ = v_var_x3f_644_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_634_;
v___y_627_ = v___y_637_;
goto v___jp_618_;
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_640_);
v___x_648_ = lean_box(0);
v___y_577_ = v_inv_x3f_631_;
v_var_x3f_578_ = v___x_648_;
v___y_579_ = v___y_632_;
v___y_580_ = v___y_633_;
v___y_581_ = v___y_634_;
v___y_582_ = v___y_635_;
v___y_583_ = v___y_636_;
v___y_584_ = v___y_637_;
v___y_585_ = v___y_638_;
goto v___jp_576_;
}
}
}
v___jp_470_:
{
lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(v___x_469_);
lean_inc(v_expanded_471_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_480_, 0, v_expanded_471_);
lean_closure_set(v___f_480_, 1, v_dec_459_);
lean_closure_set(v___f_480_, 2, v___x_479_);
v___x_481_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_458_, v_expanded_471_, v___f_480_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_481_;
}
v___jp_482_:
{
lean_object* v___x_500_; 
lean_inc(v___y_485_);
v___x_500_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_485_, v___y_497_, v___y_483_, v___y_490_, v___y_496_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; uint8_t v_breaks_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_breaks_502_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2);
lean_dec(v_a_501_);
lean_inc_ref(v___y_493_);
v___x_503_ = l_Array_append___redArg(v___y_493_, v___y_499_);
lean_dec_ref(v___y_499_);
lean_inc(v___y_489_);
lean_inc_n(v___y_495_, 2);
v___x_504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_504_, 0, v___y_495_);
lean_ctor_set(v___x_504_, 1, v___y_489_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
v___x_505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_495_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc(v___y_484_);
v___x_507_ = l_Lean_Syntax_node6(v___y_495_, v___y_484_, v___y_492_, v___y_491_, v___y_494_, v___x_504_, v___x_506_, v___y_485_);
if (v_breaks_502_ == 0)
{
if (v___x_469_ == 0)
{
lean_dec(v___y_489_);
v_expanded_471_ = v___x_507_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_497_;
v___y_474_ = v___y_483_;
v___y_475_ = v___y_490_;
v___y_476_ = v___y_496_;
v___y_477_ = v___y_486_;
v___y_478_ = v___y_487_;
goto v___jp_470_;
}
else
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_488_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_resultType_510_; lean_object* v___x_511_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v_resultType_510_ = lean_ctor_get(v_dec_459_, 1);
lean_inc_ref(v_resultType_510_);
v___x_511_ = l_Lean_Meta_isExprDefEqGuarded(v_resultType_510_, v_a_509_, v___y_490_, v___y_496_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; uint8_t v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_514_ = l_Lean_SourceInfo_fromRef(v___y_498_, v_breaks_502_);
v___x_515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
lean_inc_n(v___x_514_, 11);
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_505_);
v___x_517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_519_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__12));
v___x_520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_514_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
lean_inc_n(v___y_489_, 2);
v___x_521_ = l_Lean_Syntax_node1(v___x_514_, v___y_489_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node2(v___x_514_, v___x_518_, v___x_507_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_514_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Syntax_node1(v___x_514_, v___x_524_, v___x_526_);
v___x_528_ = l_Lean_Syntax_node1(v___x_514_, v___x_523_, v___x_527_);
lean_inc_ref(v___y_493_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_514_);
lean_ctor_set(v___x_529_, 1, v___y_489_);
lean_ctor_set(v___x_529_, 2, v___y_493_);
v___x_530_ = l_Lean_Syntax_node2(v___x_514_, v___x_518_, v___x_528_, v___x_529_);
v___x_531_ = l_Lean_Syntax_node2(v___x_514_, v___y_489_, v___x_522_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v___x_514_, v___x_517_, v___x_531_);
v___x_533_ = l_Lean_Syntax_node2(v___x_514_, v___x_515_, v___x_516_, v___x_532_);
v_expanded_471_ = v___x_533_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_497_;
v___y_474_ = v___y_483_;
v___y_475_ = v___y_490_;
v___y_476_ = v___y_496_;
v___y_477_ = v___y_486_;
v___y_478_ = v___y_487_;
goto v___jp_470_;
}
else
{
lean_dec(v___y_489_);
v_expanded_471_ = v___x_507_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_497_;
v___y_474_ = v___y_483_;
v___y_475_ = v___y_490_;
v___y_476_ = v___y_496_;
v___y_477_ = v___y_486_;
v___y_478_ = v___y_487_;
goto v___jp_470_;
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v___x_507_);
lean_dec(v___y_489_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v_a_534_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_511_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_511_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_dec(v___x_507_);
lean_dec(v___y_489_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
return v___x_508_;
}
}
}
else
{
lean_dec(v___y_489_);
v_expanded_471_ = v___x_507_;
v___y_472_ = v___y_488_;
v___y_473_ = v___y_497_;
v___y_474_ = v___y_483_;
v___y_475_ = v___y_490_;
v___y_476_ = v___y_496_;
v___y_477_ = v___y_486_;
v___y_478_ = v___y_487_;
goto v___jp_470_;
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___y_499_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
lean_dec(v___y_492_);
lean_dec(v___y_491_);
lean_dec(v___y_489_);
lean_dec(v___y_485_);
lean_dec_ref(v_dec_459_);
lean_dec(v_stx_458_);
v_a_542_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_500_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_500_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_660_, lean_object* v_dec_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_660_, v_dec_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_671_, lean_object* v_beforeStx_672_, lean_object* v_afterStx_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_672_, v_afterStx_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_684_, lean_object* v_beforeStx_685_, lean_object* v_afterStx_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_684_, v_beforeStx_685_, v_afterStx_686_, v_x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_697_, lean_object* v_stx_698_, lean_object* v_output_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_698_, v_output_699_, v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_709_, lean_object* v_stx_710_, lean_object* v_output_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_709_, v_stx_710_, v_output_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_737_, lean_object* v_x_738_, lean_object* v_mkInfoTree_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_738_, v_mkInfoTree_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_748_, lean_object* v_x_749_, lean_object* v_mkInfoTree_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_748_, v_x_749_, v_mkInfoTree_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_768_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_769_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_771_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_772_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_768_, v___x_769_, v___x_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_778_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_779_ = l_Lean_addBuiltinDocString(v___x_777_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_805_);
v___x_809_ = l_Lean_Syntax_isOfKind(v_x_805_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec(v_x_805_);
v___x_810_ = l_Lean_Macro_throwUnsupported___redArg(v_a_807_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; lean_object* v_tk_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_867_; lean_object* v_dec_x3f_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v_inv_x3f_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v_tk_812_ = l_Lean_Syntax_getArg(v_x_805_, v___x_811_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = l_Lean_Syntax_getArg(v_x_805_, v___x_813_);
v___x_905_ = lean_unsigned_to_nat(2u);
v___x_906_ = l_Lean_Syntax_getArg(v_x_805_, v___x_905_);
v___x_907_ = l_Lean_Syntax_isNone(v___x_906_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
lean_inc(v___x_906_);
v___x_908_ = l_Lean_Syntax_matchesNull(v___x_906_, v___x_813_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec(v___x_906_);
lean_dec(v___x_814_);
lean_dec(v_tk_812_);
lean_dec(v_x_805_);
v___x_909_ = l_Lean_Macro_throwUnsupported___redArg(v_a_807_);
return v___x_909_;
}
else
{
lean_object* v_inv_x3f_910_; 
v_inv_x3f_910_ = l_Lean_Syntax_getArg(v___x_906_, v___x_811_);
lean_dec(v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_910_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_inv_x3f_910_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_inv_x3f_910_);
lean_dec(v___x_814_);
lean_dec(v_tk_812_);
lean_dec(v_x_805_);
v___x_915_ = l_Lean_Macro_throwUnsupported___redArg(v_a_807_);
return v___x_915_;
}
else
{
goto v___jp_911_;
}
}
else
{
goto v___jp_911_;
}
v___jp_911_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_inv_x3f_910_);
v_inv_x3f_892_ = v___x_912_;
v___y_893_ = v_a_806_;
v___y_894_ = v_a_807_;
goto v___jp_891_;
}
}
}
else
{
lean_object* v___x_916_; 
lean_dec(v___x_906_);
v___x_916_ = lean_box(0);
v_inv_x3f_892_ = v___x_916_;
v___y_893_ = v_a_806_;
v___y_894_ = v_a_807_;
goto v___jp_891_;
}
v___jp_815_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_inc_ref_n(v___y_822_, 2);
v___x_825_ = l_Array_append___redArg(v___y_822_, v___y_824_);
lean_dec_ref(v___y_824_);
lean_inc_n(v___y_817_, 5);
lean_inc_n(v___y_823_, 15);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v___y_823_);
lean_ctor_set(v___x_826_, 1, v___y_817_);
lean_ctor_set(v___x_826_, 2, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_828_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_829_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v___y_823_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_823_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_834_, 0, v___y_823_);
lean_ctor_set(v___x_834_, 1, v___y_817_);
lean_ctor_set(v___x_834_, 2, v___y_822_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__6));
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_823_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_838_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_823_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Syntax_node1(v___y_823_, v___x_837_, v___x_839_);
lean_inc_ref_n(v___x_834_, 2);
v___x_841_ = l_Lean_Syntax_node2(v___y_823_, v___x_828_, v___x_840_, v___x_834_);
v___x_842_ = l_Lean_Syntax_node1(v___y_823_, v___y_817_, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___y_823_, v___x_827_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node2(v___y_823_, v___y_817_, v___x_836_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node6(v___y_823_, v___x_829_, v___x_831_, v___x_814_, v___x_833_, v___y_818_, v___x_834_, v___x_844_);
v___x_846_ = l_Lean_Syntax_node2(v___y_823_, v___x_828_, v___x_845_, v___x_834_);
v___x_847_ = l_Lean_Syntax_node1(v___y_823_, v___y_817_, v___x_846_);
v___x_848_ = l_Lean_Syntax_node1(v___y_823_, v___x_827_, v___x_847_);
lean_inc(v___y_821_);
v___x_849_ = l_Lean_Syntax_node4(v___y_823_, v___y_821_, v___y_820_, v___y_816_, v___x_826_, v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___y_819_);
return v___x_850_;
}
v___jp_851_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_inc_ref(v___y_858_);
v___x_861_ = l_Array_append___redArg(v___y_858_, v___y_860_);
lean_dec_ref(v___y_860_);
lean_inc(v___y_852_);
lean_inc(v___y_859_);
v___x_862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_862_, 0, v___y_859_);
lean_ctor_set(v___x_862_, 1, v___y_852_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
if (lean_obj_tag(v___y_856_) == 1)
{
lean_object* v_val_863_; lean_object* v___x_864_; 
v_val_863_ = lean_ctor_get(v___y_856_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___y_856_, 1);
v___x_864_ = l_Array_mkArray1___redArg(v_val_863_);
v___y_816_ = v___x_862_;
v___y_817_ = v___y_852_;
v___y_818_ = v___y_853_;
v___y_819_ = v___y_855_;
v___y_820_ = v___y_854_;
v___y_821_ = v___y_857_;
v___y_822_ = v___y_858_;
v___y_823_ = v___y_859_;
v___y_824_ = v___x_864_;
goto v___jp_815_;
}
else
{
lean_object* v___x_865_; 
lean_dec(v___y_856_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_816_ = v___x_862_;
v___y_817_ = v___y_852_;
v___y_818_ = v___y_853_;
v___y_819_ = v___y_855_;
v___y_820_ = v___y_854_;
v___y_821_ = v___y_857_;
v___y_822_ = v___y_858_;
v___y_823_ = v___y_859_;
v___y_824_ = v___x_865_;
goto v___jp_815_;
}
}
v___jp_866_:
{
lean_object* v_ref_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_ref_871_ = lean_ctor_get(v___y_869_, 5);
v___x_872_ = lean_unsigned_to_nat(5u);
v___x_873_ = l_Lean_Syntax_getArg(v_x_805_, v___x_872_);
lean_dec(v_x_805_);
v___x_874_ = 0;
v___x_875_ = l_Lean_SourceInfo_fromRef(v_ref_871_, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_877_ = l_Lean_SourceInfo_fromRef(v_tk_812_, v___x_809_);
lean_dec(v_tk_812_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_881_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_867_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_883_; 
v_val_882_ = lean_ctor_get(v___y_867_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___y_867_, 1);
v___x_883_ = l_Array_mkArray1___redArg(v_val_882_);
v___y_852_ = v___x_880_;
v___y_853_ = v___x_873_;
v___y_854_ = v___x_879_;
v___y_855_ = v___y_870_;
v___y_856_ = v_dec_x3f_868_;
v___y_857_ = v___x_876_;
v___y_858_ = v___x_881_;
v___y_859_ = v___x_875_;
v___y_860_ = v___x_883_;
goto v___jp_851_;
}
else
{
lean_object* v___x_884_; 
lean_dec(v___y_867_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_852_ = v___x_880_;
v___y_853_ = v___x_873_;
v___y_854_ = v___x_879_;
v___y_855_ = v___y_870_;
v___y_856_ = v_dec_x3f_868_;
v___y_857_ = v___x_876_;
v___y_858_ = v___x_881_;
v___y_859_ = v___x_875_;
v___y_860_ = v___x_884_;
goto v___jp_851_;
}
}
v___jp_885_:
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___y_887_);
v___y_867_ = v___y_889_;
v_dec_x3f_868_ = v___x_890_;
v___y_869_ = v___y_888_;
v___y_870_ = v___y_886_;
goto v___jp_866_;
}
v___jp_891_:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(3u);
v___x_896_ = l_Lean_Syntax_getArg(v_x_805_, v___x_895_);
v___x_897_ = l_Lean_Syntax_isNone(v___x_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
lean_inc(v___x_896_);
v___x_898_ = l_Lean_Syntax_matchesNull(v___x_896_, v___x_813_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec(v___x_896_);
lean_dec(v_inv_x3f_892_);
lean_dec(v___x_814_);
lean_dec(v_tk_812_);
lean_dec(v_x_805_);
v___x_899_ = l_Lean_Macro_throwUnsupported___redArg(v___y_894_);
return v___x_899_;
}
else
{
lean_object* v_dec_x3f_900_; 
v_dec_x3f_900_ = l_Lean_Syntax_getArg(v___x_896_, v___x_811_);
lean_dec(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_900_);
v___x_902_ = l_Lean_Syntax_isOfKind(v_dec_x3f_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_dec_x3f_900_);
lean_dec(v_inv_x3f_892_);
lean_dec(v___x_814_);
lean_dec(v_tk_812_);
lean_dec(v_x_805_);
v___x_903_ = l_Lean_Macro_throwUnsupported___redArg(v___y_894_);
return v___x_903_;
}
else
{
v___y_886_ = v___y_894_;
v___y_887_ = v_dec_x3f_900_;
v___y_888_ = v___y_893_;
v___y_889_ = v_inv_x3f_892_;
goto v___jp_885_;
}
}
else
{
v___y_886_ = v___y_894_;
v___y_887_ = v_dec_x3f_900_;
v___y_888_ = v___y_893_;
v___y_889_ = v_inv_x3f_892_;
goto v___jp_885_;
}
}
}
else
{
lean_object* v___x_904_; 
lean_dec(v___x_896_);
v___x_904_ = lean_box(0);
v___y_867_ = v_inv_x3f_892_;
v_dec_x3f_868_ = v___x_904_;
v___y_869_ = v___y_893_;
v___y_870_ = v___y_894_;
goto v___jp_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_Do_expandDoWhile(v_x_917_, v_a_918_, v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_928_ = l_Lean_Elab_macroAttribute;
v___x_929_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_931_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_932_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_928_, v___x_929_, v___x_930_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
lean_inc(v_x_947_);
v___x_992_ = l_Lean_Syntax_isOfKind(v_x_947_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v_x_947_);
v___x_993_ = l_Lean_Macro_throwUnsupported___redArg(v_a_949_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v_tk_1011_; lean_object* v___y_1013_; lean_object* v_dec_x3f_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___x_1039_; lean_object* v_inv_x3f_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v_tk_1011_ = l_Lean_Syntax_getArg(v_x_947_, v___x_994_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1054_ = l_Lean_Syntax_getArg(v_x_947_, v___x_1039_);
v___x_1055_ = l_Lean_Syntax_isNone(v___x_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; 
lean_inc(v___x_1054_);
v___x_1056_ = l_Lean_Syntax_matchesNull(v___x_1054_, v___x_1039_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v___x_1054_);
lean_dec(v_tk_1011_);
lean_dec(v_x_947_);
v___x_1057_ = l_Lean_Macro_throwUnsupported___redArg(v_a_949_);
return v___x_1057_;
}
else
{
lean_object* v_inv_x3f_1058_; 
v_inv_x3f_1058_ = l_Lean_Syntax_getArg(v___x_1054_, v___x_994_);
lean_dec(v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_1058_);
v___x_1062_ = l_Lean_Syntax_isOfKind(v_inv_x3f_1058_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_dec(v_inv_x3f_1058_);
lean_dec(v_tk_1011_);
lean_dec(v_x_947_);
v___x_1063_ = l_Lean_Macro_throwUnsupported___redArg(v_a_949_);
return v___x_1063_;
}
else
{
goto v___jp_1059_;
}
}
else
{
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_inv_x3f_1058_);
v_inv_x3f_1041_ = v___x_1060_;
v___y_1042_ = v_a_948_;
v___y_1043_ = v_a_949_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v___x_1064_; 
lean_dec(v___x_1054_);
v___x_1064_ = lean_box(0);
v_inv_x3f_1041_ = v___x_1064_;
v___y_1042_ = v_a_948_;
v___y_1043_ = v_a_949_;
goto v___jp_1040_;
}
v___jp_995_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_inc_ref(v___y_1001_);
v___x_1006_ = l_Array_append___redArg(v___y_1001_, v___y_1005_);
lean_dec_ref(v___y_1005_);
lean_inc(v___y_1002_);
lean_inc(v___y_1000_);
v___x_1007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___y_1000_);
lean_ctor_set(v___x_1007_, 1, v___y_1002_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
if (lean_obj_tag(v___y_999_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1009_; 
v_val_1008_ = lean_ctor_get(v___y_999_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___y_999_, 1);
v___x_1009_ = l_Array_mkArray1___redArg(v_val_1008_);
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
v___y_953_ = v___y_998_;
v___y_954_ = v___y_1000_;
v___y_955_ = v___y_1001_;
v___y_956_ = v___y_1002_;
v___y_957_ = v___y_1004_;
v___y_958_ = v___y_1003_;
v___y_959_ = v___x_1007_;
v___y_960_ = v___x_1009_;
goto v___jp_950_;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v___y_999_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
v___y_953_ = v___y_998_;
v___y_954_ = v___y_1000_;
v___y_955_ = v___y_1001_;
v___y_956_ = v___y_1002_;
v___y_957_ = v___y_1004_;
v___y_958_ = v___y_1003_;
v___y_959_ = v___x_1007_;
v___y_960_ = v___x_1010_;
goto v___jp_950_;
}
}
v___jp_1012_:
{
lean_object* v_ref_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_ref_1017_ = lean_ctor_get(v___y_1015_, 5);
v___x_1018_ = lean_unsigned_to_nat(3u);
v___x_1019_ = l_Lean_Syntax_getArg(v_x_947_, v___x_1018_);
v___x_1020_ = lean_unsigned_to_nat(5u);
v___x_1021_ = l_Lean_Syntax_getArg(v_x_947_, v___x_1020_);
lean_dec(v_x_947_);
v___x_1022_ = 0;
v___x_1023_ = l_Lean_SourceInfo_fromRef(v_ref_1017_, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1025_ = l_Lean_SourceInfo_fromRef(v_tk_1011_, v___x_992_);
lean_dec(v_tk_1011_);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_1029_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_1013_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
v_val_1030_ = lean_ctor_get(v___y_1013_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___y_1013_, 1);
v___x_1031_ = l_Array_mkArray1___redArg(v_val_1030_);
v___y_996_ = v___y_1016_;
v___y_997_ = v___x_1021_;
v___y_998_ = v___x_1019_;
v___y_999_ = v_dec_x3f_1014_;
v___y_1000_ = v___x_1023_;
v___y_1001_ = v___x_1029_;
v___y_1002_ = v___x_1028_;
v___y_1003_ = v___x_1024_;
v___y_1004_ = v___x_1027_;
v___y_1005_ = v___x_1031_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1032_; 
lean_dec(v___y_1013_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_996_ = v___y_1016_;
v___y_997_ = v___x_1021_;
v___y_998_ = v___x_1019_;
v___y_999_ = v_dec_x3f_1014_;
v___y_1000_ = v___x_1023_;
v___y_1001_ = v___x_1029_;
v___y_1002_ = v___x_1028_;
v___y_1003_ = v___x_1024_;
v___y_1004_ = v___x_1027_;
v___y_1005_ = v___x_1032_;
goto v___jp_995_;
}
}
v___jp_1033_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___y_1036_);
v___y_1013_ = v___y_1034_;
v_dec_x3f_1014_ = v___x_1038_;
v___y_1015_ = v___y_1035_;
v___y_1016_ = v___y_1037_;
goto v___jp_1012_;
}
v___jp_1040_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_unsigned_to_nat(2u);
v___x_1045_ = l_Lean_Syntax_getArg(v_x_947_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_isNone(v___x_1045_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
lean_inc(v___x_1045_);
v___x_1047_ = l_Lean_Syntax_matchesNull(v___x_1045_, v___x_1039_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec(v___x_1045_);
lean_dec(v_inv_x3f_1041_);
lean_dec(v_tk_1011_);
lean_dec(v_x_947_);
v___x_1048_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1043_);
return v___x_1048_;
}
else
{
lean_object* v_dec_x3f_1049_; 
v_dec_x3f_1049_ = l_Lean_Syntax_getArg(v___x_1045_, v___x_994_);
lean_dec(v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_1049_);
v___x_1051_ = l_Lean_Syntax_isOfKind(v_dec_x3f_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_dec_x3f_1049_);
lean_dec(v_inv_x3f_1041_);
lean_dec(v_tk_1011_);
lean_dec(v_x_947_);
v___x_1052_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1043_);
return v___x_1052_;
}
else
{
v___y_1034_ = v_inv_x3f_1041_;
v___y_1035_ = v___y_1042_;
v___y_1036_ = v_dec_x3f_1049_;
v___y_1037_ = v___y_1043_;
goto v___jp_1033_;
}
}
else
{
v___y_1034_ = v_inv_x3f_1041_;
v___y_1035_ = v___y_1042_;
v___y_1036_ = v_dec_x3f_1049_;
v___y_1037_ = v___y_1043_;
goto v___jp_1033_;
}
}
}
else
{
lean_object* v___x_1053_; 
lean_dec(v___x_1045_);
v___x_1053_ = lean_box(0);
v___y_1013_ = v_inv_x3f_1041_;
v_dec_x3f_1014_ = v___x_1053_;
v___y_1015_ = v___y_1042_;
v___y_1016_ = v___y_1043_;
goto v___jp_1012_;
}
}
}
v___jp_950_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc_ref_n(v___y_955_, 2);
v___x_961_ = l_Array_append___redArg(v___y_955_, v___y_960_);
lean_dec_ref(v___y_960_);
lean_inc_n(v___y_956_, 4);
lean_inc_n(v___y_954_, 17);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___y_954_);
lean_ctor_set(v___x_962_, 1, v___y_956_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_964_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_965_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_966_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_967_, 0, v___y_954_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_Syntax_node2(v___y_954_, v___x_965_, v___x_967_, v___y_953_);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___y_954_);
lean_ctor_set(v___x_969_, 1, v___y_956_);
lean_ctor_set(v___x_969_, 2, v___y_955_);
lean_inc_ref_n(v___x_969_, 5);
v___x_970_ = l_Lean_Syntax_node2(v___y_954_, v___x_964_, v___x_968_, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_972_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_954_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_975_ = l_Lean_Syntax_node2(v___y_954_, v___x_974_, v___x_969_, v___y_952_);
v___x_976_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_977_, 0, v___y_954_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_979_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_954_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___y_954_, v___x_978_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node2(v___y_954_, v___x_964_, v___x_981_, v___x_969_);
v___x_983_ = l_Lean_Syntax_node1(v___y_954_, v___y_956_, v___x_982_);
v___x_984_ = l_Lean_Syntax_node1(v___y_954_, v___x_963_, v___x_983_);
v___x_985_ = l_Lean_Syntax_node6(v___y_954_, v___x_971_, v___x_973_, v___x_975_, v___x_977_, v___x_984_, v___x_969_, v___x_969_);
v___x_986_ = l_Lean_Syntax_node2(v___y_954_, v___x_964_, v___x_985_, v___x_969_);
v___x_987_ = l_Lean_Syntax_node2(v___y_954_, v___y_956_, v___x_970_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node1(v___y_954_, v___x_963_, v___x_987_);
lean_inc(v___y_958_);
v___x_989_ = l_Lean_Syntax_node4(v___y_954_, v___y_958_, v___y_957_, v___y_959_, v___x_962_, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___y_951_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v_a_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1076_ = l_Lean_Elab_macroAttribute;
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_1078_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_1079_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_1080_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1076_, v___x_1077_, v___x_1078_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_1082_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
