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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 606, .m_capacity = 606, .m_length = 603, .m_data = "Builtin do-element elaborator for `repeat` (syntax kind `Lean.Parser.Term.doRepeat`).\n\nExpands to `for _ in Loop.mk do ...`. When the body cannot `break`, the loop's own expression\ntype is fixed to `PUnit`, yet the surrounding do block may require a different result type;\nwe append an `unreachable!` so the continuation has a polymorphic value of any type. The\n`unreachable!` is never actually executed (the loop never terminates normally), and any\ndead-code warning that fires on the surrounding continuation is actionable — the user can\nremove the following code without breaking the do block's type."};
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
lean_object* v_toCold_40_; lean_object* v_currRecDepth_41_; lean_object* v_ref_42_; uint16_t v_optionFlags_43_; uint8_t v_suppressElabErrors_44_; uint8_t v_isRecordingDeps_45_; lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_toCold_40_ = lean_ctor_get(v___y_37_, 0);
v_currRecDepth_41_ = lean_ctor_get(v___y_37_, 1);
v_ref_42_ = lean_ctor_get(v___y_37_, 2);
v_optionFlags_43_ = lean_ctor_get_uint16(v___y_37_, sizeof(void*)*3);
v_suppressElabErrors_44_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*3 + 2);
v_isRecordingDeps_45_ = lean_ctor_get_uint8(v___y_37_, sizeof(void*)*3 + 3);
v_ref_46_ = l_Lean_replaceRef(v_expanded_29_, v_ref_42_);
lean_inc(v_currRecDepth_41_);
lean_inc_ref(v_toCold_40_);
v___x_47_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_47_, 0, v_toCold_40_);
lean_ctor_set(v___x_47_, 1, v_currRecDepth_41_);
lean_ctor_set(v___x_47_, 2, v_ref_46_);
lean_ctor_set_uint16(v___x_47_, sizeof(void*)*3, v_optionFlags_43_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*3 + 2, v_suppressElabErrors_44_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*3 + 3, v_isRecordingDeps_45_);
v___x_48_ = l_Lean_Elab_Do_elabDoElem(v_expanded_29_, v_dec_30_, v___x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___x_47_, v___y_38_);
lean_dec_ref_known(v___x_47_, 3);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v_expanded_49_, lean_object* v_dec_50_, lean_object* v___x_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
uint8_t v___x_14824__boxed_60_; lean_object* v_res_61_; 
v___x_14824__boxed_60_ = lean_unbox(v___x_51_);
v_res_61_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_49_, v_dec_50_, v___x_14824__boxed_60_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
lean_inc_ref(v___y_63_);
v___x_71_ = lean_apply_8(v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, lean_box(0));
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_x_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec_ref(v___y_73_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* v___y_82_, lean_object* v_mkInfoTree_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v_a_89_, lean_object* v_a_x3f_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_infoState_93_; lean_object* v_trees_94_; lean_object* v___x_95_; 
v___x_92_ = lean_st_ref_get(v___y_82_);
v_infoState_93_ = lean_ctor_get(v___x_92_, 8);
lean_inc_ref(v_infoState_93_);
lean_dec(v___x_92_);
v_trees_94_ = lean_ctor_get(v_infoState_93_, 2);
lean_inc_ref(v_trees_94_);
lean_dec_ref(v_infoState_93_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_95_ = lean_apply_8(v_mkInfoTree_83_, v_trees_94_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_82_, lean_box(0));
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_135_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_135_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_135_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v_infoState_101_; lean_object* v_env_102_; lean_object* v_nextMacroScope_103_; lean_object* v_ngen_104_; lean_object* v_auxDeclNGen_105_; lean_object* v_traceState_106_; lean_object* v_cache_107_; lean_object* v_recordedDeps_108_; lean_object* v_messages_109_; lean_object* v_snapshotTasks_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_134_; 
v___x_100_ = lean_st_ref_take(v___y_82_);
v_infoState_101_ = lean_ctor_get(v___x_100_, 8);
v_env_102_ = lean_ctor_get(v___x_100_, 0);
v_nextMacroScope_103_ = lean_ctor_get(v___x_100_, 1);
v_ngen_104_ = lean_ctor_get(v___x_100_, 2);
v_auxDeclNGen_105_ = lean_ctor_get(v___x_100_, 3);
v_traceState_106_ = lean_ctor_get(v___x_100_, 4);
v_cache_107_ = lean_ctor_get(v___x_100_, 5);
v_recordedDeps_108_ = lean_ctor_get(v___x_100_, 6);
v_messages_109_ = lean_ctor_get(v___x_100_, 7);
v_snapshotTasks_110_ = lean_ctor_get(v___x_100_, 9);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_134_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_134_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_snapshotTasks_110_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_109_);
lean_inc(v_recordedDeps_108_);
lean_inc(v_cache_107_);
lean_inc(v_traceState_106_);
lean_inc(v_auxDeclNGen_105_);
lean_inc(v_ngen_104_);
lean_inc(v_nextMacroScope_103_);
lean_inc(v_env_102_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_134_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v_enabled_114_; lean_object* v_assignment_115_; lean_object* v_lazyAssignment_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_132_; 
v_enabled_114_ = lean_ctor_get_uint8(v_infoState_101_, sizeof(void*)*3);
v_assignment_115_ = lean_ctor_get(v_infoState_101_, 0);
v_lazyAssignment_116_ = lean_ctor_get(v_infoState_101_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_infoState_101_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; 
v_unused_133_ = lean_ctor_get(v_infoState_101_, 2);
lean_dec(v_unused_133_);
v___x_118_ = v_infoState_101_;
v_isShared_119_ = v_isSharedCheck_132_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_lazyAssignment_116_);
lean_inc(v_assignment_115_);
lean_dec(v_infoState_101_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_132_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = lean_box(0);
v___x_121_ = l_Lean_PersistentArray_push___redArg(v_a_89_, v_a_96_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_assignment_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_lazyAssignment_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v___x_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*3, v_enabled_114_);
v___x_123_ = v_reuseFailAlloc_131_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 8, v___x_123_);
v___x_125_ = v___x_112_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_env_102_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_nextMacroScope_103_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_ngen_104_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_auxDeclNGen_105_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_traceState_106_);
lean_ctor_set(v_reuseFailAlloc_130_, 5, v_cache_107_);
lean_ctor_set(v_reuseFailAlloc_130_, 6, v_recordedDeps_108_);
lean_ctor_set(v_reuseFailAlloc_130_, 7, v_messages_109_);
lean_ctor_set(v_reuseFailAlloc_130_, 8, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 9, v_snapshotTasks_110_);
v___x_125_ = v_reuseFailAlloc_130_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_st_ref_put(v___y_82_, v___x_125_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_120_);
v___x_128_ = v___x_98_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_120_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v_a_89_);
v_a_136_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_95_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_95_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_144_, lean_object* v_mkInfoTree_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v_a_151_, lean_object* v_a_x3f_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_144_, v_mkInfoTree_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v_a_151_, v_a_x3f_152_);
lean_dec(v_a_x3f_152_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_144_);
return v_res_154_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(32u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((size_t)5ULL);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_159_);
lean_ctor_set(v___x_163_, 3, v___x_159_);
lean_ctor_set_usize(v___x_163_, 4, v___x_158_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_infoState_167_; lean_object* v_trees_168_; lean_object* v___x_169_; lean_object* v_infoState_170_; lean_object* v_env_171_; lean_object* v_nextMacroScope_172_; lean_object* v_ngen_173_; lean_object* v_auxDeclNGen_174_; lean_object* v_traceState_175_; lean_object* v_cache_176_; lean_object* v_recordedDeps_177_; lean_object* v_messages_178_; lean_object* v_snapshotTasks_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_200_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_infoState_167_ = lean_ctor_get(v___x_166_, 8);
lean_inc_ref(v_infoState_167_);
lean_dec(v___x_166_);
v_trees_168_ = lean_ctor_get(v_infoState_167_, 2);
lean_inc_ref(v_trees_168_);
lean_dec_ref(v_infoState_167_);
v___x_169_ = lean_st_ref_take(v___y_164_);
v_infoState_170_ = lean_ctor_get(v___x_169_, 8);
v_env_171_ = lean_ctor_get(v___x_169_, 0);
v_nextMacroScope_172_ = lean_ctor_get(v___x_169_, 1);
v_ngen_173_ = lean_ctor_get(v___x_169_, 2);
v_auxDeclNGen_174_ = lean_ctor_get(v___x_169_, 3);
v_traceState_175_ = lean_ctor_get(v___x_169_, 4);
v_cache_176_ = lean_ctor_get(v___x_169_, 5);
v_recordedDeps_177_ = lean_ctor_get(v___x_169_, 6);
v_messages_178_ = lean_ctor_get(v___x_169_, 7);
v_snapshotTasks_179_ = lean_ctor_get(v___x_169_, 9);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_200_ == 0)
{
v___x_181_ = v___x_169_;
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snapshotTasks_179_);
lean_inc(v_infoState_170_);
lean_inc(v_messages_178_);
lean_inc(v_recordedDeps_177_);
lean_inc(v_cache_176_);
lean_inc(v_traceState_175_);
lean_inc(v_auxDeclNGen_174_);
lean_inc(v_ngen_173_);
lean_inc(v_nextMacroScope_172_);
lean_inc(v_env_171_);
lean_dec(v___x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v_enabled_183_; lean_object* v_assignment_184_; lean_object* v_lazyAssignment_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_198_; 
v_enabled_183_ = lean_ctor_get_uint8(v_infoState_170_, sizeof(void*)*3);
v_assignment_184_ = lean_ctor_get(v_infoState_170_, 0);
v_lazyAssignment_185_ = lean_ctor_get(v_infoState_170_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_infoState_170_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_infoState_170_, 2);
lean_dec(v_unused_199_);
v___x_187_ = v_infoState_170_;
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_lazyAssignment_185_);
lean_inc(v_assignment_184_);
lean_dec(v_infoState_170_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 2, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_assignment_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_lazyAssignment_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___x_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*3, v_enabled_183_);
v___x_191_ = v_reuseFailAlloc_197_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 8, v___x_191_);
v___x_193_ = v___x_181_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_env_171_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_nextMacroScope_172_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_ngen_173_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_auxDeclNGen_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_traceState_175_);
lean_ctor_set(v_reuseFailAlloc_196_, 5, v_cache_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 6, v_recordedDeps_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 7, v_messages_178_);
lean_ctor_set(v_reuseFailAlloc_196_, 8, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_196_, 9, v_snapshotTasks_179_);
v___x_193_ = v_reuseFailAlloc_196_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_st_ref_put(v___y_164_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_trees_168_);
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object* v_x_204_, lean_object* v_mkInfoTree_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_infoState_214_; uint8_t v_enabled_215_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_infoState_214_ = lean_ctor_get(v___x_213_, 8);
lean_inc_ref(v_infoState_214_);
lean_dec(v___x_213_);
v_enabled_215_ = lean_ctor_get_uint8(v_infoState_214_, sizeof(void*)*3);
lean_dec_ref(v_infoState_214_);
if (v_enabled_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_mkInfoTree_205_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
v___x_216_ = lean_apply_7(v_x_204_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, lean_box(0));
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v_r_219_; 
v___x_217_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_211_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref(v___x_217_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
v_r_219_ = lean_apply_7(v_x_204_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, lean_box(0));
if (lean_obj_tag(v_r_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_a_220_ = lean_ctor_get(v_r_219_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_r_219_);
if (v_isSharedCheck_244_ == 0)
{
v___x_222_ = v_r_219_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v_r_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
lean_inc(v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_243_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_211_, v_mkInfoTree_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v_a_218_, v___x_225_);
lean_dec_ref(v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v___x_226_, 0);
lean_dec(v_unused_234_);
v___x_228_ = v___x_226_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_dec(v___x_226_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v_a_220_);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_220_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_220_);
v_a_235_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_226_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_226_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_245_ = lean_ctor_get(v_r_219_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v_r_219_, 1);
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_211_, v_mkInfoTree_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v_a_218_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_247_, 0);
lean_dec(v_unused_255_);
v___x_249_ = v___x_247_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_dec(v___x_247_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v_a_245_);
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_245_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_245_);
v_a_256_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_247_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_247_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_264_, lean_object* v_mkInfoTree_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_264_, v_mkInfoTree_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object* v_stx_274_, lean_object* v_output_275_, lean_object* v_trees_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_lctx_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_lctx_284_ = lean_ctor_get(v___y_279_, 2);
lean_inc_ref(v_lctx_284_);
v___x_285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_285_, 0, v_lctx_284_);
lean_ctor_set(v___x_285_, 1, v_stx_274_);
lean_ctor_set(v___x_285_, 2, v_output_275_);
v___x_286_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_trees_276_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_stx_289_, lean_object* v_output_290_, lean_object* v_trees_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_289_, v_output_290_, v_trees_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object* v_stx_300_, lean_object* v_output_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___f_310_; lean_object* v___x_311_; 
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_310_, 0, v_stx_300_);
lean_closure_set(v___f_310_, 1, v_output_301_);
v___x_311_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_302_, v___f_310_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object* v_stx_312_, lean_object* v_output_313_, lean_object* v_x_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_312_, v_output_313_, v_x_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_beforeStx_323_, lean_object* v_afterStx_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc_ref(v___y_326_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_334_, 0, v_x_325_);
lean_closure_set(v___f_334_, 1, v___y_326_);
lean_inc(v_afterStx_324_);
lean_inc(v_beforeStx_323_);
v___x_335_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_335_, 0, lean_box(0));
lean_closure_set(v___x_335_, 1, v_beforeStx_323_);
lean_closure_set(v___x_335_, 2, v_afterStx_324_);
lean_closure_set(v___x_335_, 3, v___f_334_);
v___x_336_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_323_, v_afterStx_324_, v___x_335_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_336_) == 0)
{
return v___x_336_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_beforeStx_345_, lean_object* v_afterStx_346_, lean_object* v_x_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_345_, v_afterStx_346_, v_x_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__26(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Array_mkArray0___redArg();
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__32(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__31));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_461_, lean_object* v_dec_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v_expanded_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; 
v___x_471_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_461_);
v___x_472_ = l_Lean_Syntax_isOfKind(v_stx_461_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v___x_553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v_tk_578_; lean_object* v___y_580_; lean_object* v_var_x3f_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___x_632_; lean_object* v_inv_x3f_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v_tk_578_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_554_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_652_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_632_);
v___x_653_ = l_Lean_Syntax_isNone(v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
lean_inc(v___x_652_);
v___x_654_ = l_Lean_Syntax_matchesNull(v___x_652_, v___x_632_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v___x_652_);
lean_dec(v_tk_578_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v___x_655_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_655_;
}
else
{
lean_object* v_inv_x3f_656_; 
v_inv_x3f_656_ = l_Lean_Syntax_getArg(v___x_652_, v___x_554_);
lean_dec(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_656_);
v___x_660_ = l_Lean_Syntax_isOfKind(v_inv_x3f_656_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v_inv_x3f_656_);
lean_dec(v_tk_578_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v___x_661_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_661_;
}
else
{
goto v___jp_657_;
}
}
else
{
goto v___jp_657_;
}
v___jp_657_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_inv_x3f_656_);
v_inv_x3f_634_ = v___x_658_;
v___y_635_ = v_a_463_;
v___y_636_ = v_a_464_;
v___y_637_ = v_a_465_;
v___y_638_ = v_a_466_;
v___y_639_ = v_a_467_;
v___y_640_ = v_a_468_;
v___y_641_ = v_a_469_;
goto v___jp_633_;
}
}
}
else
{
lean_object* v___x_662_; 
lean_dec(v___x_652_);
v___x_662_ = lean_box(0);
v_inv_x3f_634_ = v___x_662_;
v___y_635_ = v_a_463_;
v___y_636_ = v_a_464_;
v___y_637_ = v_a_465_;
v___y_638_ = v_a_466_;
v___y_639_ = v_a_467_;
v___y_640_ = v_a_468_;
v___y_641_ = v_a_469_;
goto v___jp_633_;
}
v___jp_555_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc_ref(v___y_556_);
v___x_573_ = l_Array_append___redArg(v___y_556_, v___y_572_);
lean_dec_ref(v___y_572_);
lean_inc(v___y_558_);
lean_inc(v___y_566_);
v___x_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_574_, 0, v___y_566_);
lean_ctor_set(v___x_574_, 1, v___y_558_);
lean_ctor_set(v___x_574_, 2, v___x_573_);
if (lean_obj_tag(v___y_561_) == 1)
{
lean_object* v_val_575_; lean_object* v___x_576_; 
v_val_575_ = lean_ctor_get(v___y_561_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v___y_561_, 1);
v___x_576_ = l_Array_mkArray1___redArg(v_val_575_);
v___y_486_ = v___y_556_;
v___y_487_ = v___y_557_;
v___y_488_ = v___y_558_;
v___y_489_ = v___y_559_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___x_574_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___y_570_;
v___y_501_ = v___y_571_;
v___y_502_ = v___x_576_;
goto v___jp_485_;
}
else
{
lean_object* v___x_577_; 
lean_dec(v___y_561_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_486_ = v___y_556_;
v___y_487_ = v___y_557_;
v___y_488_ = v___y_558_;
v___y_489_ = v___y_559_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_562_;
v___y_492_ = v___y_563_;
v___y_493_ = v___y_564_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___x_574_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___y_570_;
v___y_501_ = v___y_571_;
v___y_502_ = v___x_577_;
goto v___jp_485_;
}
}
v___jp_579_:
{
lean_object* v_toCold_589_; lean_object* v_ref_590_; lean_object* v_quotContext_591_; lean_object* v_currMacroScope_592_; lean_object* v___x_593_; lean_object* v_seq_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_toCold_589_ = lean_ctor_get(v___y_587_, 0);
v_ref_590_ = lean_ctor_get(v___y_587_, 2);
v_quotContext_591_ = lean_ctor_get(v_toCold_589_, 8);
v_currMacroScope_592_ = lean_ctor_get(v_toCold_589_, 9);
v___x_593_ = lean_unsigned_to_nat(3u);
v_seq_594_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_593_);
v___x_595_ = 0;
v___x_596_ = l_Lean_SourceInfo_fromRef(v_ref_590_, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__20));
v___x_598_ = l_Lean_SourceInfo_fromRef(v_tk_578_, v___x_472_);
lean_dec(v_tk_578_);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_602_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__25));
v___x_603_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
lean_inc_n(v___x_596_, 7);
v___x_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_596_);
lean_ctor_set(v___x_604_, 1, v___x_601_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__28));
v___x_606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__29));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_596_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___x_596_, v___x_605_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__30));
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_596_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__32, &l_Lean_Elab_Do_elabDoRepeat___closed__32_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__32);
v___x_612_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__35));
lean_inc(v_currMacroScope_592_);
lean_inc(v_quotContext_591_);
v___x_613_ = l_Lean_addMacroScope(v_quotContext_591_, v___x_612_, v_currMacroScope_592_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__40));
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_596_);
lean_ctor_set(v___x_615_, 1, v___x_611_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = l_Lean_Syntax_node4(v___x_596_, v___x_602_, v___x_604_, v___x_608_, v___x_610_, v___x_615_);
v___x_617_ = l_Lean_Syntax_node1(v___x_596_, v___x_601_, v___x_616_);
if (lean_obj_tag(v___y_580_) == 1)
{
lean_object* v_val_618_; lean_object* v___x_619_; 
v_val_618_ = lean_ctor_get(v___y_580_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v___y_580_, 1);
v___x_619_ = l_Array_mkArray1___redArg(v_val_618_);
v___y_556_ = v___x_603_;
v___y_557_ = v___y_584_;
v___y_558_ = v___x_601_;
v___y_559_ = v_seq_594_;
v___y_560_ = v___y_583_;
v___y_561_ = v_var_x3f_581_;
v___y_562_ = v___x_600_;
v___y_563_ = v___y_585_;
v___y_564_ = v_ref_590_;
v___y_565_ = v___y_582_;
v___y_566_ = v___x_596_;
v___y_567_ = v___y_587_;
v___y_568_ = v___x_617_;
v___y_569_ = v___x_597_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_586_;
v___y_572_ = v___x_619_;
goto v___jp_555_;
}
else
{
lean_object* v___x_620_; 
lean_dec(v___y_580_);
v___x_620_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_556_ = v___x_603_;
v___y_557_ = v___y_584_;
v___y_558_ = v___x_601_;
v___y_559_ = v_seq_594_;
v___y_560_ = v___y_583_;
v___y_561_ = v_var_x3f_581_;
v___y_562_ = v___x_600_;
v___y_563_ = v___y_585_;
v___y_564_ = v_ref_590_;
v___y_565_ = v___y_582_;
v___y_566_ = v___x_596_;
v___y_567_ = v___y_587_;
v___y_568_ = v___x_617_;
v___y_569_ = v___x_597_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_586_;
v___y_572_ = v___x_620_;
goto v___jp_555_;
}
}
v___jp_621_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___y_626_);
v___y_580_ = v___y_628_;
v_var_x3f_581_ = v___x_631_;
v___y_582_ = v___y_630_;
v___y_583_ = v___y_622_;
v___y_584_ = v___y_625_;
v___y_585_ = v___y_627_;
v___y_586_ = v___y_624_;
v___y_587_ = v___y_623_;
v___y_588_ = v___y_629_;
goto v___jp_579_;
}
v___jp_633_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(2u);
v___x_643_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_642_);
v___x_644_ = l_Lean_Syntax_isNone(v___x_643_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
lean_inc(v___x_643_);
v___x_645_ = l_Lean_Syntax_matchesNull(v___x_643_, v___x_632_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v___x_643_);
lean_dec(v_inv_x3f_634_);
lean_dec(v_tk_578_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v___x_646_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_646_;
}
else
{
lean_object* v_var_x3f_647_; 
v_var_x3f_647_ = l_Lean_Syntax_getArg(v___x_643_, v___x_554_);
lean_dec(v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_var_x3f_647_);
v___x_649_ = l_Lean_Syntax_isOfKind(v_var_x3f_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v_var_x3f_647_);
lean_dec(v_inv_x3f_634_);
lean_dec(v_tk_578_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v___x_650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_650_;
}
else
{
v___y_622_ = v___y_636_;
v___y_623_ = v___y_640_;
v___y_624_ = v___y_639_;
v___y_625_ = v___y_637_;
v___y_626_ = v_var_x3f_647_;
v___y_627_ = v___y_638_;
v___y_628_ = v_inv_x3f_634_;
v___y_629_ = v___y_641_;
v___y_630_ = v___y_635_;
goto v___jp_621_;
}
}
else
{
v___y_622_ = v___y_636_;
v___y_623_ = v___y_640_;
v___y_624_ = v___y_639_;
v___y_625_ = v___y_637_;
v___y_626_ = v_var_x3f_647_;
v___y_627_ = v___y_638_;
v___y_628_ = v_inv_x3f_634_;
v___y_629_ = v___y_641_;
v___y_630_ = v___y_635_;
goto v___jp_621_;
}
}
}
else
{
lean_object* v___x_651_; 
lean_dec(v___x_643_);
v___x_651_ = lean_box(0);
v___y_580_ = v_inv_x3f_634_;
v_var_x3f_581_ = v___x_651_;
v___y_582_ = v___y_635_;
v___y_583_ = v___y_636_;
v___y_584_ = v___y_637_;
v___y_585_ = v___y_638_;
v___y_586_ = v___y_639_;
v___y_587_ = v___y_640_;
v___y_588_ = v___y_641_;
goto v___jp_579_;
}
}
}
v___jp_473_:
{
lean_object* v___x_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(v___x_472_);
lean_inc(v_expanded_474_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_483_, 0, v_expanded_474_);
lean_closure_set(v___f_483_, 1, v_dec_462_);
lean_closure_set(v___f_483_, 2, v___x_482_);
v___x_484_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_461_, v_expanded_474_, v___f_483_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc_ref(v___y_486_);
v___x_503_ = l_Array_append___redArg(v___y_486_, v___y_502_);
lean_dec_ref(v___y_502_);
lean_inc(v___y_488_);
lean_inc_n(v___y_495_, 2);
v___x_504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_504_, 0, v___y_495_);
lean_ctor_set(v___x_504_, 1, v___y_488_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
v___x_505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_495_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc(v___y_489_);
lean_inc(v___y_499_);
v___x_507_ = l_Lean_Syntax_node6(v___y_495_, v___y_499_, v___y_491_, v___y_498_, v___y_497_, v___x_504_, v___x_506_, v___y_489_);
v___x_508_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_489_, v___y_490_, v___y_487_, v___y_492_, v___y_501_, v___y_496_, v___y_500_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; uint8_t v_breaks_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v_breaks_510_ = lean_ctor_get_uint8(v_a_509_, sizeof(void*)*2);
lean_dec(v_a_509_);
if (v_breaks_510_ == 0)
{
if (v___x_472_ == 0)
{
lean_dec(v___y_488_);
v_expanded_474_ = v___x_507_;
v___y_475_ = v___y_494_;
v___y_476_ = v___y_490_;
v___y_477_ = v___y_487_;
v___y_478_ = v___y_492_;
v___y_479_ = v___y_501_;
v___y_480_ = v___y_496_;
v___y_481_ = v___y_500_;
goto v___jp_473_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_494_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_resultType_513_; lean_object* v___x_514_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v_resultType_513_ = lean_ctor_get(v_dec_462_, 1);
lean_inc_ref(v_resultType_513_);
v___x_514_ = l_Lean_Meta_isExprDefEqGuarded(v_resultType_513_, v_a_512_, v___y_492_, v___y_501_, v___y_496_, v___y_500_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; uint8_t v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_517_ = l_Lean_SourceInfo_fromRef(v___y_493_, v_breaks_510_);
v___x_518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
lean_inc_n(v___x_517_, 11);
v___x_519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_505_);
v___x_520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_521_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_522_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__12));
v___x_523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_517_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_inc_n(v___y_488_, 2);
v___x_524_ = l_Lean_Syntax_node1(v___x_517_, v___y_488_, v___x_523_);
v___x_525_ = l_Lean_Syntax_node2(v___x_517_, v___x_521_, v___x_507_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_527_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_517_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_Syntax_node1(v___x_517_, v___x_527_, v___x_529_);
v___x_531_ = l_Lean_Syntax_node1(v___x_517_, v___x_526_, v___x_530_);
lean_inc_ref(v___y_486_);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v___x_517_);
lean_ctor_set(v___x_532_, 1, v___y_488_);
lean_ctor_set(v___x_532_, 2, v___y_486_);
v___x_533_ = l_Lean_Syntax_node2(v___x_517_, v___x_521_, v___x_531_, v___x_532_);
v___x_534_ = l_Lean_Syntax_node2(v___x_517_, v___y_488_, v___x_525_, v___x_533_);
v___x_535_ = l_Lean_Syntax_node1(v___x_517_, v___x_520_, v___x_534_);
v___x_536_ = l_Lean_Syntax_node2(v___x_517_, v___x_518_, v___x_519_, v___x_535_);
v_expanded_474_ = v___x_536_;
v___y_475_ = v___y_494_;
v___y_476_ = v___y_490_;
v___y_477_ = v___y_487_;
v___y_478_ = v___y_492_;
v___y_479_ = v___y_501_;
v___y_480_ = v___y_496_;
v___y_481_ = v___y_500_;
goto v___jp_473_;
}
else
{
lean_dec(v___y_488_);
v_expanded_474_ = v___x_507_;
v___y_475_ = v___y_494_;
v___y_476_ = v___y_490_;
v___y_477_ = v___y_487_;
v___y_478_ = v___y_492_;
v___y_479_ = v___y_501_;
v___y_480_ = v___y_496_;
v___y_481_ = v___y_500_;
goto v___jp_473_;
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v___x_507_);
lean_dec(v___y_488_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v_a_537_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_514_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_514_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_dec(v___x_507_);
lean_dec(v___y_488_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
return v___x_511_;
}
}
}
else
{
lean_dec(v___y_488_);
v_expanded_474_ = v___x_507_;
v___y_475_ = v___y_494_;
v___y_476_ = v___y_490_;
v___y_477_ = v___y_487_;
v___y_478_ = v___y_492_;
v___y_479_ = v___y_501_;
v___y_480_ = v___y_496_;
v___y_481_ = v___y_500_;
goto v___jp_473_;
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___x_507_);
lean_dec(v___y_488_);
lean_dec_ref(v_dec_462_);
lean_dec(v_stx_461_);
v_a_545_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_508_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_508_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_663_, lean_object* v_dec_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_663_, v_dec_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_674_, lean_object* v_beforeStx_675_, lean_object* v_afterStx_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_675_, v_afterStx_676_, v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_687_, lean_object* v_beforeStx_688_, lean_object* v_afterStx_689_, lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_687_, v_beforeStx_688_, v_afterStx_689_, v_x_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_700_, lean_object* v_stx_701_, lean_object* v_output_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_701_, v_output_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_712_, lean_object* v_stx_713_, lean_object* v_output_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_712_, v_stx_713_, v_output_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_740_, lean_object* v_x_741_, lean_object* v_mkInfoTree_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_741_, v_mkInfoTree_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v_mkInfoTree_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_751_, v_x_752_, v_mkInfoTree_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_771_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_772_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_774_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_775_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_771_, v___x_772_, v___x_773_, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_782_ = l_Lean_addBuiltinDocString(v___x_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_808_);
v___x_812_ = l_Lean_Syntax_isOfKind(v_x_808_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_x_808_);
v___x_813_ = l_Lean_Macro_throwUnsupported___redArg(v_a_810_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v_tk_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_870_; lean_object* v_dec_x3f_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v_inv_x3f_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v_tk_815_ = l_Lean_Syntax_getArg(v_x_808_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_808_, v___x_816_);
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = l_Lean_Syntax_getArg(v_x_808_, v___x_908_);
v___x_910_ = l_Lean_Syntax_isNone(v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
lean_inc(v___x_909_);
v___x_911_ = l_Lean_Syntax_matchesNull(v___x_909_, v___x_816_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_dec(v___x_909_);
lean_dec(v___x_817_);
lean_dec(v_tk_815_);
lean_dec(v_x_808_);
v___x_912_ = l_Lean_Macro_throwUnsupported___redArg(v_a_810_);
return v___x_912_;
}
else
{
lean_object* v_inv_x3f_913_; 
v_inv_x3f_913_ = l_Lean_Syntax_getArg(v___x_909_, v___x_814_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_913_);
v___x_917_ = l_Lean_Syntax_isOfKind(v_inv_x3f_913_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
lean_dec(v_inv_x3f_913_);
lean_dec(v___x_817_);
lean_dec(v_tk_815_);
lean_dec(v_x_808_);
v___x_918_ = l_Lean_Macro_throwUnsupported___redArg(v_a_810_);
return v___x_918_;
}
else
{
goto v___jp_914_;
}
}
else
{
goto v___jp_914_;
}
v___jp_914_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_inv_x3f_913_);
v_inv_x3f_895_ = v___x_915_;
v___y_896_ = v_a_809_;
v___y_897_ = v_a_810_;
goto v___jp_894_;
}
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v___x_909_);
v___x_919_ = lean_box(0);
v_inv_x3f_895_ = v___x_919_;
v___y_896_ = v_a_809_;
v___y_897_ = v_a_810_;
goto v___jp_894_;
}
v___jp_818_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_inc_ref_n(v___y_822_, 2);
v___x_828_ = l_Array_append___redArg(v___y_822_, v___y_827_);
lean_dec_ref(v___y_827_);
lean_inc_n(v___y_820_, 5);
lean_inc_n(v___y_826_, 15);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v___y_826_);
lean_ctor_set(v___x_829_, 1, v___y_820_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_831_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_832_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_833_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_834_, 0, v___y_826_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_826_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___y_826_);
lean_ctor_set(v___x_837_, 1, v___y_820_);
lean_ctor_set(v___x_837_, 2, v___y_822_);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__6));
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_826_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_841_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_826_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___y_826_, v___x_840_, v___x_842_);
lean_inc_ref_n(v___x_837_, 2);
v___x_844_ = l_Lean_Syntax_node2(v___y_826_, v___x_831_, v___x_843_, v___x_837_);
v___x_845_ = l_Lean_Syntax_node1(v___y_826_, v___y_820_, v___x_844_);
v___x_846_ = l_Lean_Syntax_node1(v___y_826_, v___x_830_, v___x_845_);
v___x_847_ = l_Lean_Syntax_node2(v___y_826_, v___y_820_, v___x_839_, v___x_846_);
v___x_848_ = l_Lean_Syntax_node6(v___y_826_, v___x_832_, v___x_834_, v___x_817_, v___x_836_, v___y_819_, v___x_837_, v___x_847_);
v___x_849_ = l_Lean_Syntax_node2(v___y_826_, v___x_831_, v___x_848_, v___x_837_);
v___x_850_ = l_Lean_Syntax_node1(v___y_826_, v___y_820_, v___x_849_);
v___x_851_ = l_Lean_Syntax_node1(v___y_826_, v___x_830_, v___x_850_);
lean_inc(v___y_825_);
v___x_852_ = l_Lean_Syntax_node4(v___y_826_, v___y_825_, v___y_823_, v___y_821_, v___x_829_, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___y_824_);
return v___x_853_;
}
v___jp_854_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_inc_ref(v___y_857_);
v___x_864_ = l_Array_append___redArg(v___y_857_, v___y_863_);
lean_dec_ref(v___y_863_);
lean_inc(v___y_856_);
lean_inc(v___y_862_);
v___x_865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_865_, 0, v___y_862_);
lean_ctor_set(v___x_865_, 1, v___y_856_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
if (lean_obj_tag(v___y_860_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_867_; 
v_val_866_ = lean_ctor_get(v___y_860_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___y_860_, 1);
v___x_867_ = l_Array_mkArray1___redArg(v_val_866_);
v___y_819_ = v___y_855_;
v___y_820_ = v___y_856_;
v___y_821_ = v___x_865_;
v___y_822_ = v___y_857_;
v___y_823_ = v___y_858_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_861_;
v___y_826_ = v___y_862_;
v___y_827_ = v___x_867_;
goto v___jp_818_;
}
else
{
lean_object* v___x_868_; 
lean_dec(v___y_860_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_819_ = v___y_855_;
v___y_820_ = v___y_856_;
v___y_821_ = v___x_865_;
v___y_822_ = v___y_857_;
v___y_823_ = v___y_858_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_861_;
v___y_826_ = v___y_862_;
v___y_827_ = v___x_868_;
goto v___jp_818_;
}
}
v___jp_869_:
{
lean_object* v_ref_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_ref_874_ = lean_ctor_get(v___y_872_, 5);
v___x_875_ = lean_unsigned_to_nat(5u);
v___x_876_ = l_Lean_Syntax_getArg(v_x_808_, v___x_875_);
lean_dec(v_x_808_);
v___x_877_ = 0;
v___x_878_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_880_ = l_Lean_SourceInfo_fromRef(v_tk_815_, v___x_812_);
lean_dec(v_tk_815_);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_884_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_870_) == 1)
{
lean_object* v_val_885_; lean_object* v___x_886_; 
v_val_885_ = lean_ctor_get(v___y_870_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v___y_870_, 1);
v___x_886_ = l_Array_mkArray1___redArg(v_val_885_);
v___y_855_ = v___x_876_;
v___y_856_ = v___x_883_;
v___y_857_ = v___x_884_;
v___y_858_ = v___x_882_;
v___y_859_ = v___y_873_;
v___y_860_ = v_dec_x3f_871_;
v___y_861_ = v___x_879_;
v___y_862_ = v___x_878_;
v___y_863_ = v___x_886_;
goto v___jp_854_;
}
else
{
lean_object* v___x_887_; 
lean_dec(v___y_870_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_855_ = v___x_876_;
v___y_856_ = v___x_883_;
v___y_857_ = v___x_884_;
v___y_858_ = v___x_882_;
v___y_859_ = v___y_873_;
v___y_860_ = v_dec_x3f_871_;
v___y_861_ = v___x_879_;
v___y_862_ = v___x_878_;
v___y_863_ = v___x_887_;
goto v___jp_854_;
}
}
v___jp_888_:
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v___y_891_);
v___y_870_ = v___y_889_;
v_dec_x3f_871_ = v___x_893_;
v___y_872_ = v___y_890_;
v___y_873_ = v___y_892_;
goto v___jp_869_;
}
v___jp_894_:
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = lean_unsigned_to_nat(3u);
v___x_899_ = l_Lean_Syntax_getArg(v_x_808_, v___x_898_);
v___x_900_ = l_Lean_Syntax_isNone(v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
lean_inc(v___x_899_);
v___x_901_ = l_Lean_Syntax_matchesNull(v___x_899_, v___x_816_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v___x_899_);
lean_dec(v_inv_x3f_895_);
lean_dec(v___x_817_);
lean_dec(v_tk_815_);
lean_dec(v_x_808_);
v___x_902_ = l_Lean_Macro_throwUnsupported___redArg(v___y_897_);
return v___x_902_;
}
else
{
lean_object* v_dec_x3f_903_; 
v_dec_x3f_903_ = l_Lean_Syntax_getArg(v___x_899_, v___x_814_);
lean_dec(v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_903_);
v___x_905_ = l_Lean_Syntax_isOfKind(v_dec_x3f_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_dec_x3f_903_);
lean_dec(v_inv_x3f_895_);
lean_dec(v___x_817_);
lean_dec(v_tk_815_);
lean_dec(v_x_808_);
v___x_906_ = l_Lean_Macro_throwUnsupported___redArg(v___y_897_);
return v___x_906_;
}
else
{
v___y_889_ = v_inv_x3f_895_;
v___y_890_ = v___y_896_;
v___y_891_ = v_dec_x3f_903_;
v___y_892_ = v___y_897_;
goto v___jp_888_;
}
}
else
{
v___y_889_ = v_inv_x3f_895_;
v___y_890_ = v___y_896_;
v___y_891_ = v_dec_x3f_903_;
v___y_892_ = v___y_897_;
goto v___jp_888_;
}
}
}
else
{
lean_object* v___x_907_; 
lean_dec(v___x_899_);
v___x_907_ = lean_box(0);
v___y_870_ = v_inv_x3f_895_;
v_dec_x3f_871_ = v___x_907_;
v___y_872_ = v___y_896_;
v___y_873_ = v___y_897_;
goto v___jp_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_Do_expandDoWhile(v_x_920_, v_a_921_, v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_931_ = l_Lean_Elab_macroAttribute;
v___x_932_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_934_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_935_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_931_, v___x_932_, v___x_933_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
lean_inc(v_x_950_);
v___x_995_ = l_Lean_Syntax_isOfKind(v_x_950_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_dec(v_x_950_);
v___x_996_ = l_Lean_Macro_throwUnsupported___redArg(v_a_952_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v_tk_1014_; lean_object* v___y_1016_; lean_object* v_dec_x3f_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___x_1042_; lean_object* v_inv_x3f_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v_tk_1014_ = l_Lean_Syntax_getArg(v_x_950_, v___x_997_);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1057_ = l_Lean_Syntax_getArg(v_x_950_, v___x_1042_);
v___x_1058_ = l_Lean_Syntax_isNone(v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; 
lean_inc(v___x_1057_);
v___x_1059_ = l_Lean_Syntax_matchesNull(v___x_1057_, v___x_1042_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v___x_1057_);
lean_dec(v_tk_1014_);
lean_dec(v_x_950_);
v___x_1060_ = l_Lean_Macro_throwUnsupported___redArg(v_a_952_);
return v___x_1060_;
}
else
{
lean_object* v_inv_x3f_1061_; 
v_inv_x3f_1061_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_997_);
lean_dec(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_1061_);
v___x_1065_ = l_Lean_Syntax_isOfKind(v_inv_x3f_1061_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v_inv_x3f_1061_);
lean_dec(v_tk_1014_);
lean_dec(v_x_950_);
v___x_1066_ = l_Lean_Macro_throwUnsupported___redArg(v_a_952_);
return v___x_1066_;
}
else
{
goto v___jp_1062_;
}
}
else
{
goto v___jp_1062_;
}
v___jp_1062_:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_inv_x3f_1061_);
v_inv_x3f_1044_ = v___x_1063_;
v___y_1045_ = v_a_951_;
v___y_1046_ = v_a_952_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v___x_1067_; 
lean_dec(v___x_1057_);
v___x_1067_ = lean_box(0);
v_inv_x3f_1044_ = v___x_1067_;
v___y_1045_ = v_a_951_;
v___y_1046_ = v_a_952_;
goto v___jp_1043_;
}
v___jp_998_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc_ref(v___y_1000_);
v___x_1009_ = l_Array_append___redArg(v___y_1000_, v___y_1008_);
lean_dec_ref(v___y_1008_);
lean_inc(v___y_1001_);
lean_inc(v___y_1006_);
v___x_1010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___y_1006_);
lean_ctor_set(v___x_1010_, 1, v___y_1001_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
if (lean_obj_tag(v___y_1007_) == 1)
{
lean_object* v_val_1011_; lean_object* v___x_1012_; 
v_val_1011_ = lean_ctor_get(v___y_1007_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___y_1007_, 1);
v___x_1012_ = l_Array_mkArray1___redArg(v_val_1011_);
v___y_954_ = v___y_999_;
v___y_955_ = v___y_1000_;
v___y_956_ = v___y_1001_;
v___y_957_ = v___x_1010_;
v___y_958_ = v___y_1002_;
v___y_959_ = v___y_1003_;
v___y_960_ = v___y_1004_;
v___y_961_ = v___y_1005_;
v___y_962_ = v___y_1006_;
v___y_963_ = v___x_1012_;
goto v___jp_953_;
}
else
{
lean_object* v___x_1013_; 
lean_dec(v___y_1007_);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_954_ = v___y_999_;
v___y_955_ = v___y_1000_;
v___y_956_ = v___y_1001_;
v___y_957_ = v___x_1010_;
v___y_958_ = v___y_1002_;
v___y_959_ = v___y_1003_;
v___y_960_ = v___y_1004_;
v___y_961_ = v___y_1005_;
v___y_962_ = v___y_1006_;
v___y_963_ = v___x_1013_;
goto v___jp_953_;
}
}
v___jp_1015_:
{
lean_object* v_ref_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_ref_1020_ = lean_ctor_get(v___y_1018_, 5);
v___x_1021_ = lean_unsigned_to_nat(3u);
v___x_1022_ = l_Lean_Syntax_getArg(v_x_950_, v___x_1021_);
v___x_1023_ = lean_unsigned_to_nat(5u);
v___x_1024_ = l_Lean_Syntax_getArg(v_x_950_, v___x_1023_);
lean_dec(v_x_950_);
v___x_1025_ = 0;
v___x_1026_ = l_Lean_SourceInfo_fromRef(v_ref_1020_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1028_ = l_Lean_SourceInfo_fromRef(v_tk_1014_, v___x_995_);
lean_dec(v_tk_1014_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_1030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_1032_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_1016_) == 1)
{
lean_object* v_val_1033_; lean_object* v___x_1034_; 
v_val_1033_ = lean_ctor_get(v___y_1016_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v___y_1016_, 1);
v___x_1034_ = l_Array_mkArray1___redArg(v_val_1033_);
v___y_999_ = v___y_1019_;
v___y_1000_ = v___x_1032_;
v___y_1001_ = v___x_1031_;
v___y_1002_ = v___x_1024_;
v___y_1003_ = v___x_1027_;
v___y_1004_ = v___x_1030_;
v___y_1005_ = v___x_1022_;
v___y_1006_ = v___x_1026_;
v___y_1007_ = v_dec_x3f_1017_;
v___y_1008_ = v___x_1034_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v___y_1016_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_999_ = v___y_1019_;
v___y_1000_ = v___x_1032_;
v___y_1001_ = v___x_1031_;
v___y_1002_ = v___x_1024_;
v___y_1003_ = v___x_1027_;
v___y_1004_ = v___x_1030_;
v___y_1005_ = v___x_1022_;
v___y_1006_ = v___x_1026_;
v___y_1007_ = v_dec_x3f_1017_;
v___y_1008_ = v___x_1035_;
goto v___jp_998_;
}
}
v___jp_1036_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1038_);
v___y_1016_ = v___y_1037_;
v_dec_x3f_1017_ = v___x_1041_;
v___y_1018_ = v___y_1039_;
v___y_1019_ = v___y_1040_;
goto v___jp_1015_;
}
v___jp_1043_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_unsigned_to_nat(2u);
v___x_1048_ = l_Lean_Syntax_getArg(v_x_950_, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_isNone(v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; 
lean_inc(v___x_1048_);
v___x_1050_ = l_Lean_Syntax_matchesNull(v___x_1048_, v___x_1042_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec(v___x_1048_);
lean_dec(v_inv_x3f_1044_);
lean_dec(v_tk_1014_);
lean_dec(v_x_950_);
v___x_1051_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1046_);
return v___x_1051_;
}
else
{
lean_object* v_dec_x3f_1052_; 
v_dec_x3f_1052_ = l_Lean_Syntax_getArg(v___x_1048_, v___x_997_);
lean_dec(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_1052_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v_dec_x3f_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_dec_x3f_1052_);
lean_dec(v_inv_x3f_1044_);
lean_dec(v_tk_1014_);
lean_dec(v_x_950_);
v___x_1055_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1046_);
return v___x_1055_;
}
else
{
v___y_1037_ = v_inv_x3f_1044_;
v___y_1038_ = v_dec_x3f_1052_;
v___y_1039_ = v___y_1045_;
v___y_1040_ = v___y_1046_;
goto v___jp_1036_;
}
}
else
{
v___y_1037_ = v_inv_x3f_1044_;
v___y_1038_ = v_dec_x3f_1052_;
v___y_1039_ = v___y_1045_;
v___y_1040_ = v___y_1046_;
goto v___jp_1036_;
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1048_);
v___x_1056_ = lean_box(0);
v___y_1016_ = v_inv_x3f_1044_;
v_dec_x3f_1017_ = v___x_1056_;
v___y_1018_ = v___y_1045_;
v___y_1019_ = v___y_1046_;
goto v___jp_1015_;
}
}
}
v___jp_953_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc_ref_n(v___y_955_, 2);
v___x_964_ = l_Array_append___redArg(v___y_955_, v___y_963_);
lean_dec_ref(v___y_963_);
lean_inc_n(v___y_956_, 4);
lean_inc_n(v___y_962_, 17);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v___y_962_);
lean_ctor_set(v___x_965_, 1, v___y_956_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v___x_966_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_968_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_969_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_962_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_Syntax_node2(v___y_962_, v___x_968_, v___x_970_, v___y_961_);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___y_962_);
lean_ctor_set(v___x_972_, 1, v___y_956_);
lean_ctor_set(v___x_972_, 2, v___y_955_);
lean_inc_ref_n(v___x_972_, 5);
v___x_973_ = l_Lean_Syntax_node2(v___y_962_, v___x_967_, v___x_971_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_975_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___y_962_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_978_ = l_Lean_Syntax_node2(v___y_962_, v___x_977_, v___x_972_, v___y_958_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_962_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_982_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___y_962_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_Syntax_node1(v___y_962_, v___x_981_, v___x_983_);
v___x_985_ = l_Lean_Syntax_node2(v___y_962_, v___x_967_, v___x_984_, v___x_972_);
v___x_986_ = l_Lean_Syntax_node1(v___y_962_, v___y_956_, v___x_985_);
v___x_987_ = l_Lean_Syntax_node1(v___y_962_, v___x_966_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node6(v___y_962_, v___x_974_, v___x_976_, v___x_978_, v___x_980_, v___x_987_, v___x_972_, v___x_972_);
v___x_989_ = l_Lean_Syntax_node2(v___y_962_, v___x_967_, v___x_988_, v___x_972_);
v___x_990_ = l_Lean_Syntax_node2(v___y_962_, v___y_956_, v___x_973_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node1(v___y_962_, v___x_966_, v___x_990_);
lean_inc(v___y_959_);
v___x_992_ = l_Lean_Syntax_node4(v___y_962_, v___y_959_, v___y_960_, v___y_957_, v___x_965_, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_954_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1068_, v_a_1069_, v_a_1070_);
lean_dec_ref(v_a_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1079_ = l_Lean_Elab_macroAttribute;
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_1081_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_1082_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_1083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1079_, v___x_1080_, v___x_1081_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_1085_;
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
