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
v_ref_56_ = l_Lean_replaceRef(v_expanded_29_, v_ref_45_);
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
v___x_58_ = l_Lean_Elab_Do_elabDoElem(v_expanded_29_, v_dec_30_, v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___x_57_, v___y_38_);
lean_dec_ref_known(v___x_57_, 14);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v_expanded_59_, lean_object* v_dec_60_, lean_object* v___x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v___x_17169__boxed_70_; lean_object* v_res_71_; 
v___x_17169__boxed_70_ = lean_unbox(v___x_61_);
v_res_71_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_59_, v_dec_60_, v___x_17169__boxed_70_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
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
v___x_134_ = lean_st_ref_put(v___y_92_, v___x_133_);
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
v___x_202_ = lean_st_ref_put(v___y_173_, v___x_201_);
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
lean_dec_ref_known(v_r_227_, 1);
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
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__26(void){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Array_mkArray0(lean_box(0));
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__32(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__31));
v___x_436_ = l_String_toRawSubstring_x27(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_469_, lean_object* v_dec_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v_expanded_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; 
v___x_479_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_469_);
v___x_480_ = l_Lean_Syntax_isOfKind(v_stx_469_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v___x_561_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v_tk_586_; lean_object* v___y_588_; lean_object* v_var_x3f_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___x_628_; lean_object* v_inv_x3f_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v_tk_586_ = l_Lean_Syntax_getArg(v_stx_469_, v___x_562_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_649_ = l_Lean_Syntax_getArg(v_stx_469_, v___x_628_);
v___x_650_ = l_Lean_Syntax_isNone(v___x_649_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
lean_inc(v___x_649_);
v___x_651_ = l_Lean_Syntax_matchesNull(v___x_649_, v___x_628_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_649_);
lean_dec(v_tk_586_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v___x_652_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_652_;
}
else
{
lean_object* v_inv_x3f_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_inv_x3f_653_ = l_Lean_Syntax_getArg(v___x_649_, v___x_562_);
lean_dec(v___x_649_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_653_);
v___x_655_ = l_Lean_Syntax_isOfKind(v_inv_x3f_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_inv_x3f_653_);
lean_dec(v_tk_586_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v___x_656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_inv_x3f_653_);
v_inv_x3f_630_ = v___x_657_;
v___y_631_ = v_a_471_;
v___y_632_ = v_a_472_;
v___y_633_ = v_a_473_;
v___y_634_ = v_a_474_;
v___y_635_ = v_a_475_;
v___y_636_ = v_a_476_;
v___y_637_ = v_a_477_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec(v___x_649_);
v___x_658_ = lean_box(0);
v_inv_x3f_630_ = v___x_658_;
v___y_631_ = v_a_471_;
v___y_632_ = v_a_472_;
v___y_633_ = v_a_473_;
v___y_634_ = v_a_474_;
v___y_635_ = v_a_475_;
v___y_636_ = v_a_476_;
v___y_637_ = v_a_477_;
goto v___jp_629_;
}
v___jp_563_:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_inc_ref(v___y_568_);
v___x_581_ = l_Array_append___redArg(v___y_568_, v___y_580_);
lean_dec_ref(v___y_580_);
lean_inc(v___y_571_);
lean_inc(v___y_572_);
v___x_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_582_, 0, v___y_572_);
lean_ctor_set(v___x_582_, 1, v___y_571_);
lean_ctor_set(v___x_582_, 2, v___x_581_);
if (lean_obj_tag(v___y_574_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_584_; 
v_val_583_ = lean_ctor_get(v___y_574_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v___y_574_, 1);
v___x_584_ = l_Array_mkArray1___redArg(v_val_583_);
v___y_494_ = v___y_564_;
v___y_495_ = v___y_565_;
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___y_570_;
v___y_501_ = v___y_571_;
v___y_502_ = v___x_582_;
v___y_503_ = v___y_572_;
v___y_504_ = v___y_573_;
v___y_505_ = v___y_575_;
v___y_506_ = v___y_577_;
v___y_507_ = v___y_576_;
v___y_508_ = v___y_578_;
v___y_509_ = v___y_579_;
v___y_510_ = v___x_584_;
goto v___jp_493_;
}
else
{
lean_object* v___x_585_; 
lean_dec(v___y_574_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_494_ = v___y_564_;
v___y_495_ = v___y_565_;
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___y_570_;
v___y_501_ = v___y_571_;
v___y_502_ = v___x_582_;
v___y_503_ = v___y_572_;
v___y_504_ = v___y_573_;
v___y_505_ = v___y_575_;
v___y_506_ = v___y_577_;
v___y_507_ = v___y_576_;
v___y_508_ = v___y_578_;
v___y_509_ = v___y_579_;
v___y_510_ = v___x_585_;
goto v___jp_493_;
}
}
v___jp_587_:
{
lean_object* v_ref_597_; lean_object* v_quotContext_598_; lean_object* v_currMacroScope_599_; lean_object* v___x_600_; lean_object* v_seq_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_ref_597_ = lean_ctor_get(v___y_595_, 5);
v_quotContext_598_ = lean_ctor_get(v___y_595_, 10);
v_currMacroScope_599_ = lean_ctor_get(v___y_595_, 11);
v___x_600_ = lean_unsigned_to_nat(3u);
v_seq_601_ = l_Lean_Syntax_getArg(v_stx_469_, v___x_600_);
v___x_602_ = 0;
v___x_603_ = l_Lean_SourceInfo_fromRef(v_ref_597_, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__20));
v___x_605_ = l_Lean_SourceInfo_fromRef(v_tk_586_, v___x_480_);
lean_dec(v_tk_586_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__25));
v___x_610_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
lean_inc_n(v___x_603_, 7);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_603_);
lean_ctor_set(v___x_611_, 1, v___x_608_);
lean_ctor_set(v___x_611_, 2, v___x_610_);
v___x_612_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__28));
v___x_613_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__29));
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_603_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_Syntax_node1(v___x_603_, v___x_612_, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__30));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_603_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__32, &l_Lean_Elab_Do_elabDoRepeat___closed__32_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__32);
v___x_619_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__35));
lean_inc(v_currMacroScope_599_);
lean_inc(v_quotContext_598_);
v___x_620_ = l_Lean_addMacroScope(v_quotContext_598_, v___x_619_, v_currMacroScope_599_);
v___x_621_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__40));
v___x_622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_622_, 0, v___x_603_);
lean_ctor_set(v___x_622_, 1, v___x_618_);
lean_ctor_set(v___x_622_, 2, v___x_620_);
lean_ctor_set(v___x_622_, 3, v___x_621_);
v___x_623_ = l_Lean_Syntax_node4(v___x_603_, v___x_609_, v___x_611_, v___x_615_, v___x_617_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node1(v___x_603_, v___x_608_, v___x_623_);
if (lean_obj_tag(v___y_588_) == 1)
{
lean_object* v_val_625_; lean_object* v___x_626_; 
v_val_625_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v___y_588_, 1);
v___x_626_ = l_Array_mkArray1___redArg(v_val_625_);
v___y_564_ = v___y_596_;
v___y_565_ = v_seq_601_;
v___y_566_ = v_ref_597_;
v___y_567_ = v___y_592_;
v___y_568_ = v___x_610_;
v___y_569_ = v___y_595_;
v___y_570_ = v___x_607_;
v___y_571_ = v___x_608_;
v___y_572_ = v___x_603_;
v___y_573_ = v___y_594_;
v___y_574_ = v_var_x3f_589_;
v___y_575_ = v___y_591_;
v___y_576_ = v___x_624_;
v___y_577_ = v___y_590_;
v___y_578_ = v___x_604_;
v___y_579_ = v___y_593_;
v___y_580_ = v___x_626_;
goto v___jp_563_;
}
else
{
lean_object* v___x_627_; 
lean_dec(v___y_588_);
v___x_627_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_564_ = v___y_596_;
v___y_565_ = v_seq_601_;
v___y_566_ = v_ref_597_;
v___y_567_ = v___y_592_;
v___y_568_ = v___x_610_;
v___y_569_ = v___y_595_;
v___y_570_ = v___x_607_;
v___y_571_ = v___x_608_;
v___y_572_ = v___x_603_;
v___y_573_ = v___y_594_;
v___y_574_ = v_var_x3f_589_;
v___y_575_ = v___y_591_;
v___y_576_ = v___x_624_;
v___y_577_ = v___y_590_;
v___y_578_ = v___x_604_;
v___y_579_ = v___y_593_;
v___y_580_ = v___x_627_;
goto v___jp_563_;
}
}
v___jp_629_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(2u);
v___x_639_ = l_Lean_Syntax_getArg(v_stx_469_, v___x_638_);
v___x_640_ = l_Lean_Syntax_isNone(v___x_639_);
if (v___x_640_ == 0)
{
uint8_t v___x_641_; 
lean_inc(v___x_639_);
v___x_641_ = l_Lean_Syntax_matchesNull(v___x_639_, v___x_628_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec(v___x_639_);
lean_dec(v_inv_x3f_630_);
lean_dec(v_tk_586_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v___x_642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_642_;
}
else
{
lean_object* v_var_x3f_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_var_x3f_643_ = l_Lean_Syntax_getArg(v___x_639_, v___x_562_);
lean_dec(v___x_639_);
v___x_644_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_var_x3f_643_);
v___x_645_ = l_Lean_Syntax_isOfKind(v_var_x3f_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v_var_x3f_643_);
lean_dec(v_inv_x3f_630_);
lean_dec(v_tk_586_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v___x_646_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_646_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_var_x3f_643_);
v___y_588_ = v_inv_x3f_630_;
v_var_x3f_589_ = v___x_647_;
v___y_590_ = v___y_631_;
v___y_591_ = v___y_632_;
v___y_592_ = v___y_633_;
v___y_593_ = v___y_634_;
v___y_594_ = v___y_635_;
v___y_595_ = v___y_636_;
v___y_596_ = v___y_637_;
goto v___jp_587_;
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_639_);
v___x_648_ = lean_box(0);
v___y_588_ = v_inv_x3f_630_;
v_var_x3f_589_ = v___x_648_;
v___y_590_ = v___y_631_;
v___y_591_ = v___y_632_;
v___y_592_ = v___y_633_;
v___y_593_ = v___y_634_;
v___y_594_ = v___y_635_;
v___y_595_ = v___y_636_;
v___y_596_ = v___y_637_;
goto v___jp_587_;
}
}
}
v___jp_481_:
{
lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; 
v___x_490_ = lean_box(v___x_480_);
lean_inc(v_expanded_482_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_491_, 0, v_expanded_482_);
lean_closure_set(v___f_491_, 1, v_dec_470_);
lean_closure_set(v___f_491_, 2, v___x_490_);
v___x_492_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_469_, v_expanded_482_, v___f_491_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_492_;
}
v___jp_493_:
{
lean_object* v___x_511_; 
lean_inc(v___y_495_);
v___x_511_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_495_, v___y_505_, v___y_497_, v___y_509_, v___y_504_, v___y_499_, v___y_494_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; uint8_t v_breaks_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v_breaks_513_ = lean_ctor_get_uint8(v_a_512_, sizeof(void*)*2);
lean_dec(v_a_512_);
lean_inc_ref(v___y_498_);
v___x_514_ = l_Array_append___redArg(v___y_498_, v___y_510_);
lean_dec_ref(v___y_510_);
lean_inc(v___y_501_);
lean_inc_n(v___y_503_, 2);
v___x_515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_515_, 0, v___y_503_);
lean_ctor_set(v___x_515_, 1, v___y_501_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_517_, 0, v___y_503_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
lean_inc(v___y_508_);
v___x_518_ = l_Lean_Syntax_node6(v___y_503_, v___y_508_, v___y_500_, v___y_507_, v___y_502_, v___x_515_, v___x_517_, v___y_495_);
if (v_breaks_513_ == 0)
{
if (v___x_480_ == 0)
{
lean_dec(v___y_501_);
v_expanded_482_ = v___x_518_;
v___y_483_ = v___y_506_;
v___y_484_ = v___y_505_;
v___y_485_ = v___y_497_;
v___y_486_ = v___y_509_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_494_;
goto v___jp_481_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_506_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_resultType_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v_resultType_521_ = lean_ctor_get(v_dec_470_, 1);
lean_inc_ref(v_resultType_521_);
v___x_522_ = l_Lean_Meta_isExprDefEqGuarded(v_resultType_521_, v_a_520_, v___y_509_, v___y_504_, v___y_499_, v___y_494_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint8_t v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_unbox(v_a_523_);
lean_dec(v_a_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_525_ = l_Lean_SourceInfo_fromRef(v___y_496_, v_breaks_513_);
v___x_526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
lean_inc_n(v___x_525_, 11);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_516_);
v___x_528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_529_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__12));
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_525_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_inc_n(v___y_501_, 2);
v___x_532_ = l_Lean_Syntax_node1(v___x_525_, v___y_501_, v___x_531_);
v___x_533_ = l_Lean_Syntax_node2(v___x_525_, v___x_529_, v___x_518_, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_535_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_536_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_525_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_Syntax_node1(v___x_525_, v___x_535_, v___x_537_);
v___x_539_ = l_Lean_Syntax_node1(v___x_525_, v___x_534_, v___x_538_);
lean_inc_ref(v___y_498_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v___x_525_);
lean_ctor_set(v___x_540_, 1, v___y_501_);
lean_ctor_set(v___x_540_, 2, v___y_498_);
v___x_541_ = l_Lean_Syntax_node2(v___x_525_, v___x_529_, v___x_539_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node2(v___x_525_, v___y_501_, v___x_533_, v___x_541_);
v___x_543_ = l_Lean_Syntax_node1(v___x_525_, v___x_528_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node2(v___x_525_, v___x_526_, v___x_527_, v___x_543_);
v_expanded_482_ = v___x_544_;
v___y_483_ = v___y_506_;
v___y_484_ = v___y_505_;
v___y_485_ = v___y_497_;
v___y_486_ = v___y_509_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_494_;
goto v___jp_481_;
}
else
{
lean_dec(v___y_501_);
v_expanded_482_ = v___x_518_;
v___y_483_ = v___y_506_;
v___y_484_ = v___y_505_;
v___y_485_ = v___y_497_;
v___y_486_ = v___y_509_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_494_;
goto v___jp_481_;
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___x_518_);
lean_dec(v___y_501_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v_a_545_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_522_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_522_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_dec(v___x_518_);
lean_dec(v___y_501_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
return v___x_519_;
}
}
}
else
{
lean_dec(v___y_501_);
v_expanded_482_ = v___x_518_;
v___y_483_ = v___y_506_;
v___y_484_ = v___y_505_;
v___y_485_ = v___y_497_;
v___y_486_ = v___y_509_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_499_;
v___y_489_ = v___y_494_;
goto v___jp_481_;
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v___y_510_);
lean_dec(v___y_507_);
lean_dec(v___y_503_);
lean_dec(v___y_502_);
lean_dec(v___y_501_);
lean_dec(v___y_500_);
lean_dec(v___y_495_);
lean_dec_ref(v_dec_470_);
lean_dec(v_stx_469_);
v_a_553_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_511_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_511_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_659_, lean_object* v_dec_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_659_, v_dec_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_670_, lean_object* v_beforeStx_671_, lean_object* v_afterStx_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_671_, v_afterStx_672_, v_x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_683_, lean_object* v_beforeStx_684_, lean_object* v_afterStx_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_683_, v_beforeStx_684_, v_afterStx_685_, v_x_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_696_, lean_object* v_stx_697_, lean_object* v_output_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_697_, v_output_698_, v_x_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_708_, lean_object* v_stx_709_, lean_object* v_output_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_708_, v_stx_709_, v_output_710_, v_x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_736_, lean_object* v_x_737_, lean_object* v_mkInfoTree_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_737_, v_mkInfoTree_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_747_, lean_object* v_x_748_, lean_object* v_mkInfoTree_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_747_, v_x_748_, v_mkInfoTree_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_767_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_768_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_771_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_767_, v___x_768_, v___x_769_, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_778_ = l_Lean_addBuiltinDocString(v___x_776_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_804_);
v___x_808_ = l_Lean_Syntax_isOfKind(v_x_804_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_x_804_);
v___x_809_ = l_Lean_Macro_throwUnsupported___redArg(v_a_806_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v_tk_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_866_; lean_object* v_dec_x3f_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v_inv_x3f_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v_tk_811_ = l_Lean_Syntax_getArg(v_x_804_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = l_Lean_Syntax_getArg(v_x_804_, v___x_812_);
v___x_899_ = lean_unsigned_to_nat(2u);
v___x_900_ = l_Lean_Syntax_getArg(v_x_804_, v___x_899_);
v___x_901_ = l_Lean_Syntax_isNone(v___x_900_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; 
lean_inc(v___x_900_);
v___x_902_ = l_Lean_Syntax_matchesNull(v___x_900_, v___x_812_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v___x_900_);
lean_dec(v___x_813_);
lean_dec(v_tk_811_);
lean_dec(v_x_804_);
v___x_903_ = l_Lean_Macro_throwUnsupported___redArg(v_a_806_);
return v___x_903_;
}
else
{
lean_object* v_inv_x3f_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_inv_x3f_904_ = l_Lean_Syntax_getArg(v___x_900_, v___x_810_);
lean_dec(v___x_900_);
v___x_905_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_904_);
v___x_906_ = l_Lean_Syntax_isOfKind(v_inv_x3f_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_inv_x3f_904_);
lean_dec(v___x_813_);
lean_dec(v_tk_811_);
lean_dec(v_x_804_);
v___x_907_ = l_Lean_Macro_throwUnsupported___redArg(v_a_806_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_inv_x3f_904_);
v_inv_x3f_885_ = v___x_908_;
v___y_886_ = v_a_805_;
v___y_887_ = v_a_806_;
goto v___jp_884_;
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v___x_900_);
v___x_909_ = lean_box(0);
v_inv_x3f_885_ = v___x_909_;
v___y_886_ = v_a_805_;
v___y_887_ = v_a_806_;
goto v___jp_884_;
}
v___jp_814_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc_ref_n(v___y_817_, 2);
v___x_824_ = l_Array_append___redArg(v___y_817_, v___y_823_);
lean_dec_ref(v___y_823_);
lean_inc_n(v___y_815_, 5);
lean_inc_n(v___y_818_, 15);
v___x_825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_825_, 0, v___y_818_);
lean_ctor_set(v___x_825_, 1, v___y_815_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_828_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_829_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_818_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_818_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v___y_818_);
lean_ctor_set(v___x_833_, 1, v___y_815_);
lean_ctor_set(v___x_833_, 2, v___y_817_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__6));
v___x_835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_835_, 0, v___y_818_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_838_, 0, v___y_818_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_Syntax_node1(v___y_818_, v___x_836_, v___x_838_);
lean_inc_ref_n(v___x_833_, 2);
v___x_840_ = l_Lean_Syntax_node2(v___y_818_, v___x_827_, v___x_839_, v___x_833_);
v___x_841_ = l_Lean_Syntax_node1(v___y_818_, v___y_815_, v___x_840_);
v___x_842_ = l_Lean_Syntax_node1(v___y_818_, v___x_826_, v___x_841_);
v___x_843_ = l_Lean_Syntax_node2(v___y_818_, v___y_815_, v___x_835_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node6(v___y_818_, v___x_828_, v___x_830_, v___x_813_, v___x_832_, v___y_816_, v___x_833_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node2(v___y_818_, v___x_827_, v___x_844_, v___x_833_);
v___x_846_ = l_Lean_Syntax_node1(v___y_818_, v___y_815_, v___x_845_);
v___x_847_ = l_Lean_Syntax_node1(v___y_818_, v___x_826_, v___x_846_);
lean_inc(v___y_819_);
v___x_848_ = l_Lean_Syntax_node4(v___y_818_, v___y_819_, v___y_822_, v___y_821_, v___x_825_, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___y_820_);
return v___x_849_;
}
v___jp_850_:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc_ref(v___y_853_);
v___x_860_ = l_Array_append___redArg(v___y_853_, v___y_859_);
lean_dec_ref(v___y_859_);
lean_inc(v___y_851_);
lean_inc(v___y_855_);
v___x_861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_861_, 0, v___y_855_);
lean_ctor_set(v___x_861_, 1, v___y_851_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
if (lean_obj_tag(v___y_854_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_863_; 
v_val_862_ = lean_ctor_get(v___y_854_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v___y_854_, 1);
v___x_863_ = l_Array_mkArray1___redArg(v_val_862_);
v___y_815_ = v___y_851_;
v___y_816_ = v___y_852_;
v___y_817_ = v___y_853_;
v___y_818_ = v___y_855_;
v___y_819_ = v___y_856_;
v___y_820_ = v___y_857_;
v___y_821_ = v___x_861_;
v___y_822_ = v___y_858_;
v___y_823_ = v___x_863_;
goto v___jp_814_;
}
else
{
lean_object* v___x_864_; 
lean_dec(v___y_854_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_815_ = v___y_851_;
v___y_816_ = v___y_852_;
v___y_817_ = v___y_853_;
v___y_818_ = v___y_855_;
v___y_819_ = v___y_856_;
v___y_820_ = v___y_857_;
v___y_821_ = v___x_861_;
v___y_822_ = v___y_858_;
v___y_823_ = v___x_864_;
goto v___jp_814_;
}
}
v___jp_865_:
{
lean_object* v_ref_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_ref_870_ = lean_ctor_get(v___y_868_, 5);
v___x_871_ = lean_unsigned_to_nat(5u);
v___x_872_ = l_Lean_Syntax_getArg(v_x_804_, v___x_871_);
lean_dec(v_x_804_);
v___x_873_ = 0;
v___x_874_ = l_Lean_SourceInfo_fromRef(v_ref_870_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_876_ = l_Lean_SourceInfo_fromRef(v_tk_811_, v___x_808_);
lean_dec(v_tk_811_);
v___x_877_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_880_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_866_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_882_; 
v_val_881_ = lean_ctor_get(v___y_866_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v___y_866_, 1);
v___x_882_ = l_Array_mkArray1___redArg(v_val_881_);
v___y_851_ = v___x_879_;
v___y_852_ = v___x_872_;
v___y_853_ = v___x_880_;
v___y_854_ = v_dec_x3f_867_;
v___y_855_ = v___x_874_;
v___y_856_ = v___x_875_;
v___y_857_ = v___y_869_;
v___y_858_ = v___x_878_;
v___y_859_ = v___x_882_;
goto v___jp_850_;
}
else
{
lean_object* v___x_883_; 
lean_dec(v___y_866_);
v___x_883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_851_ = v___x_879_;
v___y_852_ = v___x_872_;
v___y_853_ = v___x_880_;
v___y_854_ = v_dec_x3f_867_;
v___y_855_ = v___x_874_;
v___y_856_ = v___x_875_;
v___y_857_ = v___y_869_;
v___y_858_ = v___x_878_;
v___y_859_ = v___x_883_;
goto v___jp_850_;
}
}
v___jp_884_:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_unsigned_to_nat(3u);
v___x_889_ = l_Lean_Syntax_getArg(v_x_804_, v___x_888_);
v___x_890_ = l_Lean_Syntax_isNone(v___x_889_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; 
lean_inc(v___x_889_);
v___x_891_ = l_Lean_Syntax_matchesNull(v___x_889_, v___x_812_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v___x_889_);
lean_dec(v_inv_x3f_885_);
lean_dec(v___x_813_);
lean_dec(v_tk_811_);
lean_dec(v_x_804_);
v___x_892_ = l_Lean_Macro_throwUnsupported___redArg(v___y_887_);
return v___x_892_;
}
else
{
lean_object* v_dec_x3f_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_dec_x3f_893_ = l_Lean_Syntax_getArg(v___x_889_, v___x_810_);
lean_dec(v___x_889_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_893_);
v___x_895_ = l_Lean_Syntax_isOfKind(v_dec_x3f_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_dec_x3f_893_);
lean_dec(v_inv_x3f_885_);
lean_dec(v___x_813_);
lean_dec(v_tk_811_);
lean_dec(v_x_804_);
v___x_896_ = l_Lean_Macro_throwUnsupported___redArg(v___y_887_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_dec_x3f_893_);
v___y_866_ = v_inv_x3f_885_;
v_dec_x3f_867_ = v___x_897_;
v___y_868_ = v___y_886_;
v___y_869_ = v___y_887_;
goto v___jp_865_;
}
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v___x_889_);
v___x_898_ = lean_box(0);
v___y_866_ = v_inv_x3f_885_;
v_dec_x3f_867_ = v___x_898_;
v___y_868_ = v___y_886_;
v___y_869_ = v___y_887_;
goto v___jp_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_Do_expandDoWhile(v_x_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_921_ = l_Lean_Elab_macroAttribute;
v___x_922_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_925_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_921_, v___x_922_, v___x_923_, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
lean_inc(v_x_940_);
v___x_985_ = l_Lean_Syntax_isOfKind(v_x_940_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_x_940_);
v___x_986_ = l_Lean_Macro_throwUnsupported___redArg(v_a_942_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v_tk_1004_; lean_object* v___y_1006_; lean_object* v_dec_x3f_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___x_1026_; lean_object* v_inv_x3f_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_tk_1004_ = l_Lean_Syntax_getArg(v_x_940_, v___x_987_);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1042_ = l_Lean_Syntax_getArg(v_x_940_, v___x_1026_);
v___x_1043_ = l_Lean_Syntax_isNone(v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
lean_inc(v___x_1042_);
v___x_1044_ = l_Lean_Syntax_matchesNull(v___x_1042_, v___x_1026_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec(v___x_1042_);
lean_dec(v_tk_1004_);
lean_dec(v_x_940_);
v___x_1045_ = l_Lean_Macro_throwUnsupported___redArg(v_a_942_);
return v___x_1045_;
}
else
{
lean_object* v_inv_x3f_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_inv_x3f_1046_ = l_Lean_Syntax_getArg(v___x_1042_, v___x_987_);
lean_dec(v___x_1042_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_1046_);
v___x_1048_ = l_Lean_Syntax_isOfKind(v_inv_x3f_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v_inv_x3f_1046_);
lean_dec(v_tk_1004_);
lean_dec(v_x_940_);
v___x_1049_ = l_Lean_Macro_throwUnsupported___redArg(v_a_942_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_inv_x3f_1046_);
v_inv_x3f_1028_ = v___x_1050_;
v___y_1029_ = v_a_941_;
v___y_1030_ = v_a_942_;
goto v___jp_1027_;
}
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v___x_1042_);
v___x_1051_ = lean_box(0);
v_inv_x3f_1028_ = v___x_1051_;
v___y_1029_ = v_a_941_;
v___y_1030_ = v_a_942_;
goto v___jp_1027_;
}
v___jp_988_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc_ref(v___y_993_);
v___x_999_ = l_Array_append___redArg(v___y_993_, v___y_998_);
lean_dec_ref(v___y_998_);
lean_inc(v___y_996_);
lean_inc(v___y_995_);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___y_995_);
lean_ctor_set(v___x_1000_, 1, v___y_996_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
if (lean_obj_tag(v___y_989_) == 1)
{
lean_object* v_val_1001_; lean_object* v___x_1002_; 
v_val_1001_ = lean_ctor_get(v___y_989_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___y_989_, 1);
v___x_1002_ = l_Array_mkArray1___redArg(v_val_1001_);
v___y_944_ = v___x_1000_;
v___y_945_ = v___y_990_;
v___y_946_ = v___y_992_;
v___y_947_ = v___y_991_;
v___y_948_ = v___y_993_;
v___y_949_ = v___y_994_;
v___y_950_ = v___y_995_;
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
v___y_953_ = v___x_1002_;
goto v___jp_943_;
}
else
{
lean_object* v___x_1003_; 
lean_dec(v___y_989_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_944_ = v___x_1000_;
v___y_945_ = v___y_990_;
v___y_946_ = v___y_992_;
v___y_947_ = v___y_991_;
v___y_948_ = v___y_993_;
v___y_949_ = v___y_994_;
v___y_950_ = v___y_995_;
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
v___y_953_ = v___x_1003_;
goto v___jp_943_;
}
}
v___jp_1005_:
{
lean_object* v_ref_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_ref_1010_ = lean_ctor_get(v___y_1008_, 5);
v___x_1011_ = lean_unsigned_to_nat(3u);
v___x_1012_ = l_Lean_Syntax_getArg(v_x_940_, v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(5u);
v___x_1014_ = l_Lean_Syntax_getArg(v_x_940_, v___x_1013_);
lean_dec(v_x_940_);
v___x_1015_ = 0;
v___x_1016_ = l_Lean_SourceInfo_fromRef(v_ref_1010_, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1018_ = l_Lean_SourceInfo_fromRef(v_tk_1004_, v___x_985_);
lean_dec(v_tk_1004_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_1022_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_1006_) == 1)
{
lean_object* v_val_1023_; lean_object* v___x_1024_; 
v_val_1023_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___y_1006_, 1);
v___x_1024_ = l_Array_mkArray1___redArg(v_val_1023_);
v___y_989_ = v_dec_x3f_1007_;
v___y_990_ = v___x_1017_;
v___y_991_ = v___x_1012_;
v___y_992_ = v___y_1009_;
v___y_993_ = v___x_1022_;
v___y_994_ = v___x_1014_;
v___y_995_ = v___x_1016_;
v___y_996_ = v___x_1021_;
v___y_997_ = v___x_1020_;
v___y_998_ = v___x_1024_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1025_; 
lean_dec(v___y_1006_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_989_ = v_dec_x3f_1007_;
v___y_990_ = v___x_1017_;
v___y_991_ = v___x_1012_;
v___y_992_ = v___y_1009_;
v___y_993_ = v___x_1022_;
v___y_994_ = v___x_1014_;
v___y_995_ = v___x_1016_;
v___y_996_ = v___x_1021_;
v___y_997_ = v___x_1020_;
v___y_998_ = v___x_1025_;
goto v___jp_988_;
}
}
v___jp_1027_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_unsigned_to_nat(2u);
v___x_1032_ = l_Lean_Syntax_getArg(v_x_940_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_isNone(v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
lean_inc(v___x_1032_);
v___x_1034_ = l_Lean_Syntax_matchesNull(v___x_1032_, v___x_1026_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec(v___x_1032_);
lean_dec(v_inv_x3f_1028_);
lean_dec(v_tk_1004_);
lean_dec(v_x_940_);
v___x_1035_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1030_);
return v___x_1035_;
}
else
{
lean_object* v_dec_x3f_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_dec_x3f_1036_ = l_Lean_Syntax_getArg(v___x_1032_, v___x_987_);
lean_dec(v___x_1032_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_1036_);
v___x_1038_ = l_Lean_Syntax_isOfKind(v_dec_x3f_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec(v_dec_x3f_1036_);
lean_dec(v_inv_x3f_1028_);
lean_dec(v_tk_1004_);
lean_dec(v_x_940_);
v___x_1039_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1030_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_dec_x3f_1036_);
v___y_1006_ = v_inv_x3f_1028_;
v_dec_x3f_1007_ = v___x_1040_;
v___y_1008_ = v___y_1029_;
v___y_1009_ = v___y_1030_;
goto v___jp_1005_;
}
}
}
else
{
lean_object* v___x_1041_; 
lean_dec(v___x_1032_);
v___x_1041_ = lean_box(0);
v___y_1006_ = v_inv_x3f_1028_;
v_dec_x3f_1007_ = v___x_1041_;
v___y_1008_ = v___y_1029_;
v___y_1009_ = v___y_1030_;
goto v___jp_1005_;
}
}
}
v___jp_943_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_inc_ref_n(v___y_948_, 2);
v___x_954_ = l_Array_append___redArg(v___y_948_, v___y_953_);
lean_dec_ref(v___y_953_);
lean_inc_n(v___y_951_, 4);
lean_inc_n(v___y_950_, 17);
v___x_955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_955_, 0, v___y_950_);
lean_ctor_set(v___x_955_, 1, v___y_951_);
lean_ctor_set(v___x_955_, 2, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_957_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_958_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_959_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___y_950_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_Syntax_node2(v___y_950_, v___x_958_, v___x_960_, v___y_947_);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___y_950_);
lean_ctor_set(v___x_962_, 1, v___y_951_);
lean_ctor_set(v___x_962_, 2, v___y_948_);
lean_inc_ref_n(v___x_962_, 5);
v___x_963_ = l_Lean_Syntax_node2(v___y_950_, v___x_957_, v___x_961_, v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_965_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___y_950_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_968_ = l_Lean_Syntax_node2(v___y_950_, v___x_967_, v___x_962_, v___y_949_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_950_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_972_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_950_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Syntax_node1(v___y_950_, v___x_971_, v___x_973_);
v___x_975_ = l_Lean_Syntax_node2(v___y_950_, v___x_957_, v___x_974_, v___x_962_);
v___x_976_ = l_Lean_Syntax_node1(v___y_950_, v___y_951_, v___x_975_);
v___x_977_ = l_Lean_Syntax_node1(v___y_950_, v___x_956_, v___x_976_);
v___x_978_ = l_Lean_Syntax_node6(v___y_950_, v___x_964_, v___x_966_, v___x_968_, v___x_970_, v___x_977_, v___x_962_, v___x_962_);
v___x_979_ = l_Lean_Syntax_node2(v___y_950_, v___x_957_, v___x_978_, v___x_962_);
v___x_980_ = l_Lean_Syntax_node2(v___y_950_, v___y_951_, v___x_963_, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___y_950_, v___x_956_, v___x_980_);
lean_inc(v___y_945_);
v___x_982_ = l_Lean_Syntax_node4(v___y_950_, v___y_945_, v___y_952_, v___y_944_, v___x_955_, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___y_946_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1052_, v_a_1053_, v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1063_ = l_Lean_Elab_macroAttribute;
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_1066_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_1067_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1063_, v___x_1064_, v___x_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_1069_;
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
