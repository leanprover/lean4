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
lean_object* v_toCold_40_; lean_object* v_options_41_; lean_object* v_currRecDepth_42_; lean_object* v_maxRecDepth_43_; lean_object* v_ref_44_; lean_object* v_currNamespace_45_; lean_object* v_openDecls_46_; lean_object* v_initHeartbeats_47_; lean_object* v_maxHeartbeats_48_; lean_object* v_currMacroScope_49_; uint8_t v_diag_50_; uint8_t v_suppressElabErrors_51_; lean_object* v_ref_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_toCold_40_ = lean_ctor_get(v___y_37_, 0);
v_options_41_ = lean_ctor_get(v___y_37_, 1);
v_currRecDepth_42_ = lean_ctor_get(v___y_37_, 2);
v_maxRecDepth_43_ = lean_ctor_get(v___y_37_, 3);
v_ref_44_ = lean_ctor_get(v___y_37_, 4);
v_currNamespace_45_ = lean_ctor_get(v___y_37_, 5);
v_openDecls_46_ = lean_ctor_get(v___y_37_, 6);
v_initHeartbeats_47_ = lean_ctor_get(v___y_37_, 7);
v_maxHeartbeats_48_ = lean_ctor_get(v___y_37_, 8);
v_currMacroScope_49_ = lean_ctor_get(v___y_37_, 9);
v_diag_50_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*10);
v_suppressElabErrors_51_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*10 + 1);
v_ref_52_ = l_Lean_replaceRef(v_expanded_29_, v_ref_44_);
lean_inc(v_currMacroScope_49_);
lean_inc(v_maxHeartbeats_48_);
lean_inc(v_initHeartbeats_47_);
lean_inc(v_openDecls_46_);
lean_inc(v_currNamespace_45_);
lean_inc(v_maxRecDepth_43_);
lean_inc(v_currRecDepth_42_);
lean_inc_ref(v_options_41_);
lean_inc_ref(v_toCold_40_);
v___x_53_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_53_, 0, v_toCold_40_);
lean_ctor_set(v___x_53_, 1, v_options_41_);
lean_ctor_set(v___x_53_, 2, v_currRecDepth_42_);
lean_ctor_set(v___x_53_, 3, v_maxRecDepth_43_);
lean_ctor_set(v___x_53_, 4, v_ref_52_);
lean_ctor_set(v___x_53_, 5, v_currNamespace_45_);
lean_ctor_set(v___x_53_, 6, v_openDecls_46_);
lean_ctor_set(v___x_53_, 7, v_initHeartbeats_47_);
lean_ctor_set(v___x_53_, 8, v_maxHeartbeats_48_);
lean_ctor_set(v___x_53_, 9, v_currMacroScope_49_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*10, v_diag_50_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*10 + 1, v_suppressElabErrors_51_);
v___x_54_ = l_Lean_Elab_Do_elabDoElem(v_expanded_29_, v_dec_30_, v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___x_53_, v___y_38_);
lean_dec_ref_known(v___x_53_, 10);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v_expanded_55_, lean_object* v_dec_56_, lean_object* v___x_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
uint8_t v___x_14942__boxed_66_; lean_object* v_res_67_; 
v___x_14942__boxed_66_ = lean_unbox(v___x_57_);
v_res_67_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_55_, v_dec_56_, v___x_14942__boxed_66_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc_ref(v___y_69_);
v___x_77_ = lean_apply_8(v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec_ref(v___y_79_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* v___y_88_, lean_object* v_mkInfoTree_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v_a_95_, lean_object* v_a_x3f_96_){
_start:
{
lean_object* v___x_98_; lean_object* v_infoState_99_; lean_object* v_trees_100_; lean_object* v___x_101_; 
v___x_98_ = lean_st_ref_get(v___y_88_);
v_infoState_99_ = lean_ctor_get(v___x_98_, 7);
lean_inc_ref(v_infoState_99_);
lean_dec(v___x_98_);
v_trees_100_ = lean_ctor_get(v_infoState_99_, 2);
lean_inc_ref(v_trees_100_);
lean_dec_ref(v_infoState_99_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_94_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
v___x_101_ = lean_apply_8(v_mkInfoTree_89_, v_trees_100_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_88_, lean_box(0));
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_140_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_140_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_140_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_140_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v_infoState_107_; lean_object* v_env_108_; lean_object* v_nextMacroScope_109_; lean_object* v_ngen_110_; lean_object* v_auxDeclNGen_111_; lean_object* v_traceState_112_; lean_object* v_cache_113_; lean_object* v_messages_114_; lean_object* v_snapshotTasks_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_139_; 
v___x_106_ = lean_st_ref_take(v___y_88_);
v_infoState_107_ = lean_ctor_get(v___x_106_, 7);
v_env_108_ = lean_ctor_get(v___x_106_, 0);
v_nextMacroScope_109_ = lean_ctor_get(v___x_106_, 1);
v_ngen_110_ = lean_ctor_get(v___x_106_, 2);
v_auxDeclNGen_111_ = lean_ctor_get(v___x_106_, 3);
v_traceState_112_ = lean_ctor_get(v___x_106_, 4);
v_cache_113_ = lean_ctor_get(v___x_106_, 5);
v_messages_114_ = lean_ctor_get(v___x_106_, 6);
v_snapshotTasks_115_ = lean_ctor_get(v___x_106_, 8);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_139_ == 0)
{
v___x_117_ = v___x_106_;
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_snapshotTasks_115_);
lean_inc(v_infoState_107_);
lean_inc(v_messages_114_);
lean_inc(v_cache_113_);
lean_inc(v_traceState_112_);
lean_inc(v_auxDeclNGen_111_);
lean_inc(v_ngen_110_);
lean_inc(v_nextMacroScope_109_);
lean_inc(v_env_108_);
lean_dec(v___x_106_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v_enabled_119_; lean_object* v_assignment_120_; lean_object* v_lazyAssignment_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_137_; 
v_enabled_119_ = lean_ctor_get_uint8(v_infoState_107_, sizeof(void*)*3);
v_assignment_120_ = lean_ctor_get(v_infoState_107_, 0);
v_lazyAssignment_121_ = lean_ctor_get(v_infoState_107_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_infoState_107_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v_infoState_107_, 2);
lean_dec(v_unused_138_);
v___x_123_ = v_infoState_107_;
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_lazyAssignment_121_);
lean_inc(v_assignment_120_);
lean_dec(v_infoState_107_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = l_Lean_PersistentArray_push___redArg(v_a_95_, v_a_102_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 2, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_assignment_120_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_lazyAssignment_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v___x_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_136_, sizeof(void*)*3, v_enabled_119_);
v___x_127_ = v_reuseFailAlloc_136_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 7, v___x_127_);
v___x_129_ = v___x_117_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_env_108_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_nextMacroScope_109_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_ngen_110_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_auxDeclNGen_111_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_traceState_112_);
lean_ctor_set(v_reuseFailAlloc_135_, 5, v_cache_113_);
lean_ctor_set(v_reuseFailAlloc_135_, 6, v_messages_114_);
lean_ctor_set(v_reuseFailAlloc_135_, 7, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 8, v_snapshotTasks_115_);
v___x_129_ = v_reuseFailAlloc_135_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_st_ref_put(v___y_88_, v___x_129_);
v___x_131_ = lean_box(0);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_131_);
v___x_133_ = v___x_104_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v_a_95_);
v_a_141_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_101_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_101_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_149_, lean_object* v_mkInfoTree_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v_a_156_, lean_object* v_a_x3f_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_149_, v_mkInfoTree_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v_a_156_, v_a_x3f_157_);
lean_dec(v_a_x3f_157_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_149_);
return v_res_159_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_163_ = ((size_t)5ULL);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_unsigned_to_nat(32u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_168_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_164_);
lean_ctor_set(v___x_168_, 3, v___x_164_);
lean_ctor_set_usize(v___x_168_, 4, v___x_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_infoState_172_; lean_object* v_trees_173_; lean_object* v___x_174_; lean_object* v_infoState_175_; lean_object* v_env_176_; lean_object* v_nextMacroScope_177_; lean_object* v_ngen_178_; lean_object* v_auxDeclNGen_179_; lean_object* v_traceState_180_; lean_object* v_cache_181_; lean_object* v_messages_182_; lean_object* v_snapshotTasks_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_204_; 
v___x_171_ = lean_st_ref_get(v___y_169_);
v_infoState_172_ = lean_ctor_get(v___x_171_, 7);
lean_inc_ref(v_infoState_172_);
lean_dec(v___x_171_);
v_trees_173_ = lean_ctor_get(v_infoState_172_, 2);
lean_inc_ref(v_trees_173_);
lean_dec_ref(v_infoState_172_);
v___x_174_ = lean_st_ref_take(v___y_169_);
v_infoState_175_ = lean_ctor_get(v___x_174_, 7);
v_env_176_ = lean_ctor_get(v___x_174_, 0);
v_nextMacroScope_177_ = lean_ctor_get(v___x_174_, 1);
v_ngen_178_ = lean_ctor_get(v___x_174_, 2);
v_auxDeclNGen_179_ = lean_ctor_get(v___x_174_, 3);
v_traceState_180_ = lean_ctor_get(v___x_174_, 4);
v_cache_181_ = lean_ctor_get(v___x_174_, 5);
v_messages_182_ = lean_ctor_get(v___x_174_, 6);
v_snapshotTasks_183_ = lean_ctor_get(v___x_174_, 8);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_204_ == 0)
{
v___x_185_ = v___x_174_;
v_isShared_186_ = v_isSharedCheck_204_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_snapshotTasks_183_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_182_);
lean_inc(v_cache_181_);
lean_inc(v_traceState_180_);
lean_inc(v_auxDeclNGen_179_);
lean_inc(v_ngen_178_);
lean_inc(v_nextMacroScope_177_);
lean_inc(v_env_176_);
lean_dec(v___x_174_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_204_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v_enabled_187_; lean_object* v_assignment_188_; lean_object* v_lazyAssignment_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_202_; 
v_enabled_187_ = lean_ctor_get_uint8(v_infoState_175_, sizeof(void*)*3);
v_assignment_188_ = lean_ctor_get(v_infoState_175_, 0);
v_lazyAssignment_189_ = lean_ctor_get(v_infoState_175_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_infoState_175_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_infoState_175_, 2);
lean_dec(v_unused_203_);
v___x_191_ = v_infoState_175_;
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_lazyAssignment_189_);
lean_inc(v_assignment_188_);
lean_dec(v_infoState_175_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_assignment_188_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_lazyAssignment_189_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*3, v_enabled_187_);
v___x_195_ = v_reuseFailAlloc_201_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 7, v___x_195_);
v___x_197_ = v___x_185_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_env_176_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_nextMacroScope_177_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_ngen_178_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_auxDeclNGen_179_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_traceState_180_);
lean_ctor_set(v_reuseFailAlloc_200_, 5, v_cache_181_);
lean_ctor_set(v_reuseFailAlloc_200_, 6, v_messages_182_);
lean_ctor_set(v_reuseFailAlloc_200_, 7, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_200_, 8, v_snapshotTasks_183_);
v___x_197_ = v_reuseFailAlloc_200_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_st_ref_put(v___y_169_, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v_trees_173_);
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_205_);
lean_dec(v___y_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object* v_x_208_, lean_object* v_mkInfoTree_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v_infoState_218_; uint8_t v_enabled_219_; 
v___x_217_ = lean_st_ref_get(v___y_215_);
v_infoState_218_ = lean_ctor_get(v___x_217_, 7);
lean_inc_ref(v_infoState_218_);
lean_dec(v___x_217_);
v_enabled_219_ = lean_ctor_get_uint8(v_infoState_218_, sizeof(void*)*3);
lean_dec_ref(v_infoState_218_);
if (v_enabled_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec_ref(v_mkInfoTree_209_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
v___x_220_ = lean_apply_7(v_x_208_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, lean_box(0));
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v_a_222_; lean_object* v_r_223_; 
v___x_221_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_215_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
v_r_223_ = lean_apply_7(v_x_208_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, lean_box(0));
if (lean_obj_tag(v_r_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_248_; 
v_a_224_ = lean_ctor_get(v_r_223_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_r_223_);
if (v_isSharedCheck_248_ == 0)
{
v___x_226_ = v_r_223_;
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v_r_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
lean_inc(v_a_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 1);
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_247_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_215_, v_mkInfoTree_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v_a_222_, v___x_229_);
lean_dec_ref(v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_230_, 0);
lean_dec(v_unused_238_);
v___x_232_ = v___x_230_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_dec(v___x_230_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v_a_224_);
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_224_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_224_);
v_a_239_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_230_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_230_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_249_ = lean_ctor_get(v_r_223_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v_r_223_, 1);
v___x_250_ = lean_box(0);
v___x_251_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_215_, v_mkInfoTree_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v_a_222_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_251_, 0);
lean_dec(v_unused_259_);
v___x_253_ = v___x_251_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_dec(v___x_251_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 1);
lean_ctor_set(v___x_253_, 0, v_a_249_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_249_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v_a_249_);
v_a_260_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_251_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_251_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_268_, lean_object* v_mkInfoTree_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_268_, v_mkInfoTree_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object* v_stx_278_, lean_object* v_output_279_, lean_object* v_trees_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_lctx_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_lctx_288_ = lean_ctor_get(v___y_283_, 2);
lean_inc_ref(v_lctx_288_);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v_lctx_288_);
lean_ctor_set(v___x_289_, 1, v_stx_278_);
lean_ctor_set(v___x_289_, 2, v_output_279_);
v___x_290_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_trees_280_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_stx_293_, lean_object* v_output_294_, lean_object* v_trees_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_293_, v_output_294_, v_trees_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object* v_stx_304_, lean_object* v_output_305_, lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_314_, 0, v_stx_304_);
lean_closure_set(v___f_314_, 1, v_output_305_);
v___x_315_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_306_, v___f_314_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object* v_stx_316_, lean_object* v_output_317_, lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_316_, v_output_317_, v_x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_beforeStx_327_, lean_object* v_afterStx_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_inc_ref(v___y_330_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_338_, 0, v_x_329_);
lean_closure_set(v___f_338_, 1, v___y_330_);
lean_inc(v_afterStx_328_);
lean_inc(v_beforeStx_327_);
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_339_, 0, lean_box(0));
lean_closure_set(v___x_339_, 1, v_beforeStx_327_);
lean_closure_set(v___x_339_, 2, v_afterStx_328_);
lean_closure_set(v___x_339_, 3, v___f_338_);
v___x_340_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_327_, v_afterStx_328_, v___x_339_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
return v___x_340_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_beforeStx_349_, lean_object* v_afterStx_350_, lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_349_, v_afterStx_350_, v_x_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_360_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__26(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Array_mkArray0(lean_box(0));
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__32(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__31));
v___x_432_ = l_String_toRawSubstring_x27(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_465_, lean_object* v_dec_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v_expanded_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; 
v___x_475_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_465_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_stx_465_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_557_; 
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v___x_557_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v_tk_582_; lean_object* v___y_584_; lean_object* v_var_x3f_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___x_636_; lean_object* v_inv_x3f_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v_tk_582_ = l_Lean_Syntax_getArg(v_stx_465_, v___x_558_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_656_ = l_Lean_Syntax_getArg(v_stx_465_, v___x_636_);
v___x_657_ = l_Lean_Syntax_isNone(v___x_656_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
lean_inc(v___x_656_);
v___x_658_ = l_Lean_Syntax_matchesNull(v___x_656_, v___x_636_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v___x_656_);
lean_dec(v_tk_582_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v___x_659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_659_;
}
else
{
lean_object* v_inv_x3f_660_; 
v_inv_x3f_660_ = l_Lean_Syntax_getArg(v___x_656_, v___x_558_);
lean_dec(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_660_);
v___x_664_ = l_Lean_Syntax_isOfKind(v_inv_x3f_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v_inv_x3f_660_);
lean_dec(v_tk_582_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v___x_665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_665_;
}
else
{
goto v___jp_661_;
}
}
else
{
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_inv_x3f_660_);
v_inv_x3f_638_ = v___x_662_;
v___y_639_ = v_a_467_;
v___y_640_ = v_a_468_;
v___y_641_ = v_a_469_;
v___y_642_ = v_a_470_;
v___y_643_ = v_a_471_;
v___y_644_ = v_a_472_;
v___y_645_ = v_a_473_;
goto v___jp_637_;
}
}
}
else
{
lean_object* v___x_666_; 
lean_dec(v___x_656_);
v___x_666_ = lean_box(0);
v_inv_x3f_638_ = v___x_666_;
v___y_639_ = v_a_467_;
v___y_640_ = v_a_468_;
v___y_641_ = v_a_469_;
v___y_642_ = v_a_470_;
v___y_643_ = v_a_471_;
v___y_644_ = v_a_472_;
v___y_645_ = v_a_473_;
goto v___jp_637_;
}
v___jp_559_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_inc_ref(v___y_562_);
v___x_577_ = l_Array_append___redArg(v___y_562_, v___y_576_);
lean_dec_ref(v___y_576_);
lean_inc(v___y_563_);
lean_inc(v___y_569_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___y_569_);
lean_ctor_set(v___x_578_, 1, v___y_563_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
if (lean_obj_tag(v___y_561_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_580_; 
v_val_579_ = lean_ctor_get(v___y_561_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___y_561_, 1);
v___x_580_ = l_Array_mkArray1___redArg(v_val_579_);
v___y_490_ = v___y_560_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
v___y_501_ = v___x_578_;
v___y_502_ = v___y_572_;
v___y_503_ = v___y_573_;
v___y_504_ = v___y_574_;
v___y_505_ = v___y_575_;
v___y_506_ = v___x_580_;
goto v___jp_489_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v___y_561_);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_490_ = v___y_560_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
v___y_501_ = v___x_578_;
v___y_502_ = v___y_572_;
v___y_503_ = v___y_573_;
v___y_504_ = v___y_574_;
v___y_505_ = v___y_575_;
v___y_506_ = v___x_581_;
goto v___jp_489_;
}
}
v___jp_583_:
{
lean_object* v_toCold_593_; lean_object* v_ref_594_; lean_object* v_currMacroScope_595_; lean_object* v_quotContext_596_; lean_object* v___x_597_; lean_object* v_seq_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_toCold_593_ = lean_ctor_get(v___y_591_, 0);
v_ref_594_ = lean_ctor_get(v___y_591_, 4);
v_currMacroScope_595_ = lean_ctor_get(v___y_591_, 9);
v_quotContext_596_ = lean_ctor_get(v_toCold_593_, 2);
v___x_597_ = lean_unsigned_to_nat(3u);
v_seq_598_ = l_Lean_Syntax_getArg(v_stx_465_, v___x_597_);
v___x_599_ = 0;
v___x_600_ = l_Lean_SourceInfo_fromRef(v_ref_594_, v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__20));
v___x_602_ = l_Lean_SourceInfo_fromRef(v_tk_582_, v___x_476_);
lean_dec(v_tk_582_);
v___x_603_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__25));
v___x_607_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
lean_inc_n(v___x_600_, 7);
v___x_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_600_);
lean_ctor_set(v___x_608_, 1, v___x_605_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__28));
v___x_610_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__29));
v___x_611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_600_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_Syntax_node1(v___x_600_, v___x_609_, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__30));
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_600_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__32, &l_Lean_Elab_Do_elabDoRepeat___closed__32_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__32);
v___x_616_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__35));
lean_inc(v_currMacroScope_595_);
lean_inc(v_quotContext_596_);
v___x_617_ = l_Lean_addMacroScope(v_quotContext_596_, v___x_616_, v_currMacroScope_595_);
v___x_618_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__40));
v___x_619_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_619_, 0, v___x_600_);
lean_ctor_set(v___x_619_, 1, v___x_615_);
lean_ctor_set(v___x_619_, 2, v___x_617_);
lean_ctor_set(v___x_619_, 3, v___x_618_);
v___x_620_ = l_Lean_Syntax_node4(v___x_600_, v___x_606_, v___x_608_, v___x_612_, v___x_614_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node1(v___x_600_, v___x_605_, v___x_620_);
if (lean_obj_tag(v___y_584_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_623_; 
v_val_622_ = lean_ctor_get(v___y_584_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___y_584_, 1);
v___x_623_ = l_Array_mkArray1___redArg(v_val_622_);
v___y_560_ = v___y_588_;
v___y_561_ = v_var_x3f_585_;
v___y_562_ = v___x_607_;
v___y_563_ = v___x_605_;
v___y_564_ = v_seq_598_;
v___y_565_ = v___y_591_;
v___y_566_ = v___y_592_;
v___y_567_ = v___y_586_;
v___y_568_ = v___x_621_;
v___y_569_ = v___x_600_;
v___y_570_ = v___y_589_;
v___y_571_ = v_ref_594_;
v___y_572_ = v___x_604_;
v___y_573_ = v___y_590_;
v___y_574_ = v___y_587_;
v___y_575_ = v___x_601_;
v___y_576_ = v___x_623_;
goto v___jp_559_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v___y_584_);
v___x_624_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_560_ = v___y_588_;
v___y_561_ = v_var_x3f_585_;
v___y_562_ = v___x_607_;
v___y_563_ = v___x_605_;
v___y_564_ = v_seq_598_;
v___y_565_ = v___y_591_;
v___y_566_ = v___y_592_;
v___y_567_ = v___y_586_;
v___y_568_ = v___x_621_;
v___y_569_ = v___x_600_;
v___y_570_ = v___y_589_;
v___y_571_ = v_ref_594_;
v___y_572_ = v___x_604_;
v___y_573_ = v___y_590_;
v___y_574_ = v___y_587_;
v___y_575_ = v___x_601_;
v___y_576_ = v___x_624_;
goto v___jp_559_;
}
}
v___jp_625_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___y_630_);
v___y_584_ = v___y_629_;
v_var_x3f_585_ = v___x_635_;
v___y_586_ = v___y_632_;
v___y_587_ = v___y_628_;
v___y_588_ = v___y_633_;
v___y_589_ = v___y_626_;
v___y_590_ = v___y_627_;
v___y_591_ = v___y_634_;
v___y_592_ = v___y_631_;
goto v___jp_583_;
}
v___jp_637_:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = l_Lean_Syntax_getArg(v_stx_465_, v___x_646_);
v___x_648_ = l_Lean_Syntax_isNone(v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
lean_inc(v___x_647_);
v___x_649_ = l_Lean_Syntax_matchesNull(v___x_647_, v___x_636_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v___x_647_);
lean_dec(v_inv_x3f_638_);
lean_dec(v_tk_582_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v___x_650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_650_;
}
else
{
lean_object* v_var_x3f_651_; 
v_var_x3f_651_ = l_Lean_Syntax_getArg(v___x_647_, v___x_558_);
lean_dec(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_var_x3f_651_);
v___x_653_ = l_Lean_Syntax_isOfKind(v_var_x3f_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v_var_x3f_651_);
lean_dec(v_inv_x3f_638_);
lean_dec(v_tk_582_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v___x_654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_654_;
}
else
{
v___y_626_ = v___y_642_;
v___y_627_ = v___y_643_;
v___y_628_ = v___y_640_;
v___y_629_ = v_inv_x3f_638_;
v___y_630_ = v_var_x3f_651_;
v___y_631_ = v___y_645_;
v___y_632_ = v___y_639_;
v___y_633_ = v___y_641_;
v___y_634_ = v___y_644_;
goto v___jp_625_;
}
}
else
{
v___y_626_ = v___y_642_;
v___y_627_ = v___y_643_;
v___y_628_ = v___y_640_;
v___y_629_ = v_inv_x3f_638_;
v___y_630_ = v_var_x3f_651_;
v___y_631_ = v___y_645_;
v___y_632_ = v___y_639_;
v___y_633_ = v___y_641_;
v___y_634_ = v___y_644_;
goto v___jp_625_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v___x_647_);
v___x_655_ = lean_box(0);
v___y_584_ = v_inv_x3f_638_;
v_var_x3f_585_ = v___x_655_;
v___y_586_ = v___y_639_;
v___y_587_ = v___y_640_;
v___y_588_ = v___y_641_;
v___y_589_ = v___y_642_;
v___y_590_ = v___y_643_;
v___y_591_ = v___y_644_;
v___y_592_ = v___y_645_;
goto v___jp_583_;
}
}
}
v___jp_477_:
{
lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(v___x_476_);
lean_inc(v_expanded_478_);
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_487_, 0, v_expanded_478_);
lean_closure_set(v___f_487_, 1, v_dec_466_);
lean_closure_set(v___f_487_, 2, v___x_486_);
v___x_488_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_465_, v_expanded_478_, v___f_487_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_488_;
}
v___jp_489_:
{
lean_object* v___x_507_; 
lean_inc(v___y_493_);
v___x_507_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_493_, v___y_504_, v___y_490_, v___y_499_, v___y_503_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; uint8_t v_breaks_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_breaks_509_ = lean_ctor_get_uint8(v_a_508_, sizeof(void*)*2);
lean_dec(v_a_508_);
lean_inc_ref(v___y_491_);
v___x_510_ = l_Array_append___redArg(v___y_491_, v___y_506_);
lean_dec_ref(v___y_506_);
lean_inc(v___y_492_);
lean_inc_n(v___y_498_, 2);
v___x_511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_511_, 0, v___y_498_);
lean_ctor_set(v___x_511_, 1, v___y_492_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
v___x_512_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_513_, 0, v___y_498_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
lean_inc(v___y_505_);
v___x_514_ = l_Lean_Syntax_node6(v___y_498_, v___y_505_, v___y_502_, v___y_497_, v___y_501_, v___x_511_, v___x_513_, v___y_493_);
if (v_breaks_509_ == 0)
{
if (v___x_476_ == 0)
{
lean_dec(v___y_492_);
v_expanded_478_ = v___x_514_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_504_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_499_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
goto v___jp_477_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_496_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_resultType_517_; lean_object* v___x_518_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v_resultType_517_ = lean_ctor_get(v_dec_466_, 1);
lean_inc_ref(v_resultType_517_);
v___x_518_ = l_Lean_Meta_isExprDefEqGuarded(v_resultType_517_, v_a_516_, v___y_499_, v___y_503_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; uint8_t v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = lean_unbox(v_a_519_);
lean_dec(v_a_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_521_ = l_Lean_SourceInfo_fromRef(v___y_500_, v_breaks_509_);
v___x_522_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
lean_inc_n(v___x_521_, 11);
v___x_523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_512_);
v___x_524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__12));
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_521_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_inc_n(v___y_492_, 2);
v___x_528_ = l_Lean_Syntax_node1(v___x_521_, v___y_492_, v___x_527_);
v___x_529_ = l_Lean_Syntax_node2(v___x_521_, v___x_525_, v___x_514_, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_531_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_532_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_521_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_Syntax_node1(v___x_521_, v___x_531_, v___x_533_);
v___x_535_ = l_Lean_Syntax_node1(v___x_521_, v___x_530_, v___x_534_);
lean_inc_ref(v___y_491_);
v___x_536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_536_, 0, v___x_521_);
lean_ctor_set(v___x_536_, 1, v___y_492_);
lean_ctor_set(v___x_536_, 2, v___y_491_);
v___x_537_ = l_Lean_Syntax_node2(v___x_521_, v___x_525_, v___x_535_, v___x_536_);
v___x_538_ = l_Lean_Syntax_node2(v___x_521_, v___y_492_, v___x_529_, v___x_537_);
v___x_539_ = l_Lean_Syntax_node1(v___x_521_, v___x_524_, v___x_538_);
v___x_540_ = l_Lean_Syntax_node2(v___x_521_, v___x_522_, v___x_523_, v___x_539_);
v_expanded_478_ = v___x_540_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_504_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_499_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
goto v___jp_477_;
}
else
{
lean_dec(v___y_492_);
v_expanded_478_ = v___x_514_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_504_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_499_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
goto v___jp_477_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___x_514_);
lean_dec(v___y_492_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v_a_541_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_518_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_518_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_dec(v___x_514_);
lean_dec(v___y_492_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
return v___x_515_;
}
}
}
else
{
lean_dec(v___y_492_);
v_expanded_478_ = v___x_514_;
v___y_479_ = v___y_496_;
v___y_480_ = v___y_504_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_499_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_494_;
v___y_485_ = v___y_495_;
goto v___jp_477_;
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___y_506_);
lean_dec(v___y_502_);
lean_dec(v___y_501_);
lean_dec(v___y_498_);
lean_dec(v___y_497_);
lean_dec(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v_dec_466_);
lean_dec(v_stx_465_);
v_a_549_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_507_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_507_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_667_, lean_object* v_dec_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_667_, v_dec_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_678_, lean_object* v_beforeStx_679_, lean_object* v_afterStx_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_679_, v_afterStx_680_, v_x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_691_, lean_object* v_beforeStx_692_, lean_object* v_afterStx_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_691_, v_beforeStx_692_, v_afterStx_693_, v_x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_704_, lean_object* v_stx_705_, lean_object* v_output_706_, lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_705_, v_output_706_, v_x_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_716_, lean_object* v_stx_717_, lean_object* v_output_718_, lean_object* v_x_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_716_, v_stx_717_, v_output_718_, v_x_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_744_, lean_object* v_x_745_, lean_object* v_mkInfoTree_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_745_, v_mkInfoTree_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_755_, lean_object* v_x_756_, lean_object* v_mkInfoTree_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_755_, v_x_756_, v_mkInfoTree_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_775_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_776_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_778_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_779_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_775_, v___x_776_, v___x_777_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_786_ = l_Lean_addBuiltinDocString(v___x_784_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_812_);
v___x_816_ = l_Lean_Syntax_isOfKind(v_x_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_x_812_);
v___x_817_ = l_Lean_Macro_throwUnsupported___redArg(v_a_814_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v_tk_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_874_; lean_object* v_dec_x3f_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v_inv_x3f_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v_tk_819_ = l_Lean_Syntax_getArg(v_x_812_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = l_Lean_Syntax_getArg(v_x_812_, v___x_820_);
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = l_Lean_Syntax_getArg(v_x_812_, v___x_912_);
v___x_914_ = l_Lean_Syntax_isNone(v___x_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; 
lean_inc(v___x_913_);
v___x_915_ = l_Lean_Syntax_matchesNull(v___x_913_, v___x_820_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v___x_913_);
lean_dec(v___x_821_);
lean_dec(v_tk_819_);
lean_dec(v_x_812_);
v___x_916_ = l_Lean_Macro_throwUnsupported___redArg(v_a_814_);
return v___x_916_;
}
else
{
lean_object* v_inv_x3f_917_; 
v_inv_x3f_917_ = l_Lean_Syntax_getArg(v___x_913_, v___x_818_);
lean_dec(v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_917_);
v___x_921_ = l_Lean_Syntax_isOfKind(v_inv_x3f_917_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec(v_inv_x3f_917_);
lean_dec(v___x_821_);
lean_dec(v_tk_819_);
lean_dec(v_x_812_);
v___x_922_ = l_Lean_Macro_throwUnsupported___redArg(v_a_814_);
return v___x_922_;
}
else
{
goto v___jp_918_;
}
}
else
{
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_inv_x3f_917_);
v_inv_x3f_899_ = v___x_919_;
v___y_900_ = v_a_813_;
v___y_901_ = v_a_814_;
goto v___jp_898_;
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v___x_913_);
v___x_923_ = lean_box(0);
v_inv_x3f_899_ = v___x_923_;
v___y_900_ = v_a_813_;
v___y_901_ = v_a_814_;
goto v___jp_898_;
}
v___jp_822_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref_n(v___y_829_, 2);
v___x_832_ = l_Array_append___redArg(v___y_829_, v___y_831_);
lean_dec_ref(v___y_831_);
lean_inc_n(v___y_824_, 5);
lean_inc_n(v___y_830_, 15);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v___y_830_);
lean_ctor_set(v___x_833_, 1, v___y_824_);
lean_ctor_set(v___x_833_, 2, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_836_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_838_, 0, v___y_830_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_840_, 0, v___y_830_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_841_, 0, v___y_830_);
lean_ctor_set(v___x_841_, 1, v___y_824_);
lean_ctor_set(v___x_841_, 2, v___y_829_);
v___x_842_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__6));
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___y_830_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_845_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_830_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Lean_Syntax_node1(v___y_830_, v___x_844_, v___x_846_);
lean_inc_ref_n(v___x_841_, 2);
v___x_848_ = l_Lean_Syntax_node2(v___y_830_, v___x_835_, v___x_847_, v___x_841_);
v___x_849_ = l_Lean_Syntax_node1(v___y_830_, v___y_824_, v___x_848_);
v___x_850_ = l_Lean_Syntax_node1(v___y_830_, v___x_834_, v___x_849_);
v___x_851_ = l_Lean_Syntax_node2(v___y_830_, v___y_824_, v___x_843_, v___x_850_);
v___x_852_ = l_Lean_Syntax_node6(v___y_830_, v___x_836_, v___x_838_, v___x_821_, v___x_840_, v___y_825_, v___x_841_, v___x_851_);
v___x_853_ = l_Lean_Syntax_node2(v___y_830_, v___x_835_, v___x_852_, v___x_841_);
v___x_854_ = l_Lean_Syntax_node1(v___y_830_, v___y_824_, v___x_853_);
v___x_855_ = l_Lean_Syntax_node1(v___y_830_, v___x_834_, v___x_854_);
lean_inc(v___y_828_);
v___x_856_ = l_Lean_Syntax_node4(v___y_830_, v___y_828_, v___y_827_, v___y_823_, v___x_833_, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___y_826_);
return v___x_857_;
}
v___jp_858_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v___y_865_);
v___x_868_ = l_Array_append___redArg(v___y_865_, v___y_867_);
lean_dec_ref(v___y_867_);
lean_inc(v___y_859_);
lean_inc(v___y_866_);
v___x_869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_869_, 0, v___y_866_);
lean_ctor_set(v___x_869_, 1, v___y_859_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
if (lean_obj_tag(v___y_863_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_871_; 
v_val_870_ = lean_ctor_get(v___y_863_, 0);
lean_inc(v_val_870_);
lean_dec_ref_known(v___y_863_, 1);
v___x_871_ = l_Array_mkArray1___redArg(v_val_870_);
v___y_823_ = v___x_869_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_862_;
v___y_827_ = v___y_861_;
v___y_828_ = v___y_864_;
v___y_829_ = v___y_865_;
v___y_830_ = v___y_866_;
v___y_831_ = v___x_871_;
goto v___jp_822_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v___y_863_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_823_ = v___x_869_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_862_;
v___y_827_ = v___y_861_;
v___y_828_ = v___y_864_;
v___y_829_ = v___y_865_;
v___y_830_ = v___y_866_;
v___y_831_ = v___x_872_;
goto v___jp_822_;
}
}
v___jp_873_:
{
lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_ref_878_ = lean_ctor_get(v___y_876_, 5);
v___x_879_ = lean_unsigned_to_nat(5u);
v___x_880_ = l_Lean_Syntax_getArg(v_x_812_, v___x_879_);
lean_dec(v_x_812_);
v___x_881_ = 0;
v___x_882_ = l_Lean_SourceInfo_fromRef(v_ref_878_, v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_884_ = l_Lean_SourceInfo_fromRef(v_tk_819_, v___x_816_);
lean_dec(v_tk_819_);
v___x_885_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_888_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_874_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_890_; 
v_val_889_ = lean_ctor_get(v___y_874_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___y_874_, 1);
v___x_890_ = l_Array_mkArray1___redArg(v_val_889_);
v___y_859_ = v___x_887_;
v___y_860_ = v___x_880_;
v___y_861_ = v___x_886_;
v___y_862_ = v___y_877_;
v___y_863_ = v_dec_x3f_875_;
v___y_864_ = v___x_883_;
v___y_865_ = v___x_888_;
v___y_866_ = v___x_882_;
v___y_867_ = v___x_890_;
goto v___jp_858_;
}
else
{
lean_object* v___x_891_; 
lean_dec(v___y_874_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_859_ = v___x_887_;
v___y_860_ = v___x_880_;
v___y_861_ = v___x_886_;
v___y_862_ = v___y_877_;
v___y_863_ = v_dec_x3f_875_;
v___y_864_ = v___x_883_;
v___y_865_ = v___x_888_;
v___y_866_ = v___x_882_;
v___y_867_ = v___x_891_;
goto v___jp_858_;
}
}
v___jp_892_:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v___y_894_);
v___y_874_ = v___y_896_;
v_dec_x3f_875_ = v___x_897_;
v___y_876_ = v___y_895_;
v___y_877_ = v___y_893_;
goto v___jp_873_;
}
v___jp_898_:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_unsigned_to_nat(3u);
v___x_903_ = l_Lean_Syntax_getArg(v_x_812_, v___x_902_);
v___x_904_ = l_Lean_Syntax_isNone(v___x_903_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
lean_inc(v___x_903_);
v___x_905_ = l_Lean_Syntax_matchesNull(v___x_903_, v___x_820_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v___x_903_);
lean_dec(v_inv_x3f_899_);
lean_dec(v___x_821_);
lean_dec(v_tk_819_);
lean_dec(v_x_812_);
v___x_906_ = l_Lean_Macro_throwUnsupported___redArg(v___y_901_);
return v___x_906_;
}
else
{
lean_object* v_dec_x3f_907_; 
v_dec_x3f_907_ = l_Lean_Syntax_getArg(v___x_903_, v___x_818_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_907_);
v___x_909_ = l_Lean_Syntax_isOfKind(v_dec_x3f_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_dec_x3f_907_);
lean_dec(v_inv_x3f_899_);
lean_dec(v___x_821_);
lean_dec(v_tk_819_);
lean_dec(v_x_812_);
v___x_910_ = l_Lean_Macro_throwUnsupported___redArg(v___y_901_);
return v___x_910_;
}
else
{
v___y_893_ = v___y_901_;
v___y_894_ = v_dec_x3f_907_;
v___y_895_ = v___y_900_;
v___y_896_ = v_inv_x3f_899_;
goto v___jp_892_;
}
}
else
{
v___y_893_ = v___y_901_;
v___y_894_ = v_dec_x3f_907_;
v___y_895_ = v___y_900_;
v___y_896_ = v_inv_x3f_899_;
goto v___jp_892_;
}
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v___x_903_);
v___x_911_ = lean_box(0);
v___y_874_ = v_inv_x3f_899_;
v_dec_x3f_875_ = v___x_911_;
v___y_876_ = v___y_900_;
v___y_877_ = v___y_901_;
goto v___jp_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_Do_expandDoWhile(v_x_924_, v_a_925_, v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_935_ = l_Lean_Elab_macroAttribute;
v___x_936_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_938_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_939_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_935_, v___x_936_, v___x_937_, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
lean_inc(v_x_954_);
v___x_999_ = l_Lean_Syntax_isOfKind(v_x_954_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v_x_954_);
v___x_1000_ = l_Lean_Macro_throwUnsupported___redArg(v_a_956_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v_tk_1018_; lean_object* v___y_1020_; lean_object* v_dec_x3f_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1046_; lean_object* v_inv_x3f_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v_tk_1018_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1001_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1061_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1046_);
v___x_1062_ = l_Lean_Syntax_isNone(v___x_1061_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; 
lean_inc(v___x_1061_);
v___x_1063_ = l_Lean_Syntax_matchesNull(v___x_1061_, v___x_1046_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec(v___x_1061_);
lean_dec(v_tk_1018_);
lean_dec(v_x_954_);
v___x_1064_ = l_Lean_Macro_throwUnsupported___redArg(v_a_956_);
return v___x_1064_;
}
else
{
lean_object* v_inv_x3f_1065_; 
v_inv_x3f_1065_ = l_Lean_Syntax_getArg(v___x_1061_, v___x_1001_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_1065_);
v___x_1069_ = l_Lean_Syntax_isOfKind(v_inv_x3f_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
lean_dec(v_inv_x3f_1065_);
lean_dec(v_tk_1018_);
lean_dec(v_x_954_);
v___x_1070_ = l_Lean_Macro_throwUnsupported___redArg(v_a_956_);
return v___x_1070_;
}
else
{
goto v___jp_1066_;
}
}
else
{
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_inv_x3f_1065_);
v_inv_x3f_1048_ = v___x_1067_;
v___y_1049_ = v_a_955_;
v___y_1050_ = v_a_956_;
goto v___jp_1047_;
}
}
}
else
{
lean_object* v___x_1071_; 
lean_dec(v___x_1061_);
v___x_1071_ = lean_box(0);
v_inv_x3f_1048_ = v___x_1071_;
v___y_1049_ = v_a_955_;
v___y_1050_ = v_a_956_;
goto v___jp_1047_;
}
v___jp_1002_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc_ref(v___y_1008_);
v___x_1013_ = l_Array_append___redArg(v___y_1008_, v___y_1012_);
lean_dec_ref(v___y_1012_);
lean_inc(v___y_1009_);
lean_inc(v___y_1007_);
v___x_1014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___y_1007_);
lean_ctor_set(v___x_1014_, 1, v___y_1009_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
if (lean_obj_tag(v___y_1006_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1016_; 
v_val_1015_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v___y_1006_, 1);
v___x_1016_ = l_Array_mkArray1___redArg(v_val_1015_);
v___y_958_ = v___y_1003_;
v___y_959_ = v___y_1004_;
v___y_960_ = v___y_1005_;
v___y_961_ = v___y_1007_;
v___y_962_ = v___y_1008_;
v___y_963_ = v___y_1009_;
v___y_964_ = v___y_1011_;
v___y_965_ = v___y_1010_;
v___y_966_ = v___x_1014_;
v___y_967_ = v___x_1016_;
goto v___jp_957_;
}
else
{
lean_object* v___x_1017_; 
lean_dec(v___y_1006_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_958_ = v___y_1003_;
v___y_959_ = v___y_1004_;
v___y_960_ = v___y_1005_;
v___y_961_ = v___y_1007_;
v___y_962_ = v___y_1008_;
v___y_963_ = v___y_1009_;
v___y_964_ = v___y_1011_;
v___y_965_ = v___y_1010_;
v___y_966_ = v___x_1014_;
v___y_967_ = v___x_1017_;
goto v___jp_957_;
}
}
v___jp_1019_:
{
lean_object* v_ref_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_ref_1024_ = lean_ctor_get(v___y_1022_, 5);
v___x_1025_ = lean_unsigned_to_nat(3u);
v___x_1026_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1025_);
v___x_1027_ = lean_unsigned_to_nat(5u);
v___x_1028_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1027_);
lean_dec(v_x_954_);
v___x_1029_ = 0;
v___x_1030_ = l_Lean_SourceInfo_fromRef(v_ref_1024_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1032_ = l_Lean_SourceInfo_fromRef(v_tk_1018_, v___x_999_);
lean_dec(v_tk_1018_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_1020_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; 
v_val_1037_ = lean_ctor_get(v___y_1020_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___y_1020_, 1);
v___x_1038_ = l_Array_mkArray1___redArg(v_val_1037_);
v___y_1003_ = v___y_1023_;
v___y_1004_ = v___x_1028_;
v___y_1005_ = v___x_1026_;
v___y_1006_ = v_dec_x3f_1021_;
v___y_1007_ = v___x_1030_;
v___y_1008_ = v___x_1036_;
v___y_1009_ = v___x_1035_;
v___y_1010_ = v___x_1031_;
v___y_1011_ = v___x_1034_;
v___y_1012_ = v___x_1038_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1039_; 
lean_dec(v___y_1020_);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_1003_ = v___y_1023_;
v___y_1004_ = v___x_1028_;
v___y_1005_ = v___x_1026_;
v___y_1006_ = v_dec_x3f_1021_;
v___y_1007_ = v___x_1030_;
v___y_1008_ = v___x_1036_;
v___y_1009_ = v___x_1035_;
v___y_1010_ = v___x_1031_;
v___y_1011_ = v___x_1034_;
v___y_1012_ = v___x_1039_;
goto v___jp_1002_;
}
}
v___jp_1040_:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___y_1043_);
v___y_1020_ = v___y_1041_;
v_dec_x3f_1021_ = v___x_1045_;
v___y_1022_ = v___y_1042_;
v___y_1023_ = v___y_1044_;
goto v___jp_1019_;
}
v___jp_1047_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(2u);
v___x_1052_ = l_Lean_Syntax_getArg(v_x_954_, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_isNone(v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
lean_inc(v___x_1052_);
v___x_1054_ = l_Lean_Syntax_matchesNull(v___x_1052_, v___x_1046_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v___x_1052_);
lean_dec(v_inv_x3f_1048_);
lean_dec(v_tk_1018_);
lean_dec(v_x_954_);
v___x_1055_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1050_);
return v___x_1055_;
}
else
{
lean_object* v_dec_x3f_1056_; 
v_dec_x3f_1056_ = l_Lean_Syntax_getArg(v___x_1052_, v___x_1001_);
lean_dec(v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_1056_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_dec_x3f_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v_dec_x3f_1056_);
lean_dec(v_inv_x3f_1048_);
lean_dec(v_tk_1018_);
lean_dec(v_x_954_);
v___x_1059_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1050_);
return v___x_1059_;
}
else
{
v___y_1041_ = v_inv_x3f_1048_;
v___y_1042_ = v___y_1049_;
v___y_1043_ = v_dec_x3f_1056_;
v___y_1044_ = v___y_1050_;
goto v___jp_1040_;
}
}
else
{
v___y_1041_ = v_inv_x3f_1048_;
v___y_1042_ = v___y_1049_;
v___y_1043_ = v_dec_x3f_1056_;
v___y_1044_ = v___y_1050_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v___x_1060_; 
lean_dec(v___x_1052_);
v___x_1060_ = lean_box(0);
v___y_1020_ = v_inv_x3f_1048_;
v_dec_x3f_1021_ = v___x_1060_;
v___y_1022_ = v___y_1049_;
v___y_1023_ = v___y_1050_;
goto v___jp_1019_;
}
}
}
v___jp_957_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_inc_ref_n(v___y_962_, 2);
v___x_968_ = l_Array_append___redArg(v___y_962_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_inc_n(v___y_963_, 4);
lean_inc_n(v___y_961_, 17);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___y_961_);
lean_ctor_set(v___x_969_, 1, v___y_963_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_971_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_972_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_973_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___y_961_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_Syntax_node2(v___y_961_, v___x_972_, v___x_974_, v___y_960_);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v___y_961_);
lean_ctor_set(v___x_976_, 1, v___y_963_);
lean_ctor_set(v___x_976_, 2, v___y_962_);
lean_inc_ref_n(v___x_976_, 5);
v___x_977_ = l_Lean_Syntax_node2(v___y_961_, v___x_971_, v___x_975_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_979_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_961_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_982_ = l_Lean_Syntax_node2(v___y_961_, v___x_981_, v___x_976_, v___y_959_);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_961_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_986_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_961_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_Syntax_node1(v___y_961_, v___x_985_, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___y_961_, v___x_971_, v___x_988_, v___x_976_);
v___x_990_ = l_Lean_Syntax_node1(v___y_961_, v___y_963_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node1(v___y_961_, v___x_970_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node6(v___y_961_, v___x_978_, v___x_980_, v___x_982_, v___x_984_, v___x_991_, v___x_976_, v___x_976_);
v___x_993_ = l_Lean_Syntax_node2(v___y_961_, v___x_971_, v___x_992_, v___x_976_);
v___x_994_ = l_Lean_Syntax_node2(v___y_961_, v___y_963_, v___x_977_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node1(v___y_961_, v___x_970_, v___x_994_);
lean_inc(v___y_965_);
v___x_996_ = l_Lean_Syntax_node4(v___y_961_, v___y_965_, v___y_964_, v___y_966_, v___x_969_, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___y_958_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1072_, v_a_1073_, v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1083_ = l_Lean_Elab_macroAttribute;
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_1087_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1083_, v___x_1084_, v___x_1085_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_1089_;
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
