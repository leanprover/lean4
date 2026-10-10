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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(v_00_u03b1_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_30_;
}
}
lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object* v_expanded_31_, lean_object* v_dec_32_, uint8_t v___x_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_toCold_42_; lean_object* v_currRecDepth_43_; lean_object* v_ref_44_; uint16_t v_optionFlags_45_; uint8_t v_suppressElabErrors_46_; uint8_t v_isRecordingDeps_47_; lean_object* v_ref_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_toCold_42_ = lean_ctor_get(v___y_39_, 0);
v_currRecDepth_43_ = lean_ctor_get(v___y_39_, 1);
v_ref_44_ = lean_ctor_get(v___y_39_, 2);
v_optionFlags_45_ = lean_ctor_get_uint16(v___y_39_, sizeof(void*)*3);
v_suppressElabErrors_46_ = lean_ctor_get_uint8(v___y_39_, sizeof(void*)*3 + 2);
v_isRecordingDeps_47_ = lean_ctor_get_uint8(v___y_39_, sizeof(void*)*3 + 3);
v_ref_48_ = l_Lean_replaceRef(v_expanded_31_, v_ref_44_);
lean_inc(v_currRecDepth_43_);
lean_inc_ref(v_toCold_42_);
v___x_49_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_49_, 0, v_toCold_42_);
lean_ctor_set(v___x_49_, 1, v_currRecDepth_43_);
lean_ctor_set(v___x_49_, 2, v_ref_48_);
lean_ctor_set_uint16(v___x_49_, sizeof(void*)*3, v_optionFlags_45_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*3 + 2, v_suppressElabErrors_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*3 + 3, v_isRecordingDeps_47_);
v___x_50_ = l_Lean_Elab_Do_elabDoElem(v_expanded_31_, v_dec_32_, v___x_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___x_49_, v___y_40_);
lean_dec_ref_known(v___x_49_, 3);
return v___x_50_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoRepeat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expanded_31_ = stack[0].m_obj;
lean_object* v_dec_32_ = stack[1].m_obj;
uint8_t v___x_33_ = stack[2].m_num;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_31_, v_dec_32_, v___x_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v_expanded_52_, lean_object* v_dec_53_, lean_object* v___x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
uint8_t v___x_14848__boxed_63_; lean_object* v_res_64_; 
v___x_14848__boxed_63_ = lean_unbox(v___x_54_);
v_res_64_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v_expanded_52_, v_dec_53_, v___x_14848__boxed_63_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_64_;
}
}
lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc_ref(v___y_66_);
v___x_74_ = lean_apply_8(v_x_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_65_ = stack[0].m_obj;
lean_object* v___y_66_ = stack[1].m_obj;
lean_object* v___y_67_ = stack[2].m_obj;
lean_object* v___y_68_ = stack[3].m_obj;
lean_object* v___y_69_ = stack[4].m_obj;
lean_object* v___y_70_ = stack[5].m_obj;
lean_object* v___y_71_ = stack[6].m_obj;
lean_object* v___y_72_ = stack[7].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_x_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec_ref(v___y_77_);
return v_res_85_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* v___y_86_, lean_object* v_mkInfoTree_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v_a_93_, lean_object* v_a_x3f_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_infoState_97_; lean_object* v_trees_98_; lean_object* v___x_99_; 
v___x_96_ = lean_st_ref_get(v___y_86_);
v_infoState_97_ = lean_ctor_get(v___x_96_, 8);
lean_inc_ref(v_infoState_97_);
lean_dec(v___x_96_);
v_trees_98_ = lean_ctor_get(v_infoState_97_, 2);
lean_inc_ref(v_trees_98_);
lean_dec_ref(v_infoState_97_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
v___x_99_ = lean_apply_8(v_mkInfoTree_87_, v_trees_98_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_86_, lean_box(0));
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_139_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_139_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_139_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_139_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v_infoState_105_; lean_object* v_env_106_; lean_object* v_nextMacroScope_107_; lean_object* v_ngen_108_; lean_object* v_auxDeclNGen_109_; lean_object* v_traceState_110_; lean_object* v_cache_111_; lean_object* v_recordedDeps_112_; lean_object* v_messages_113_; lean_object* v_snapshotTasks_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_138_; 
v___x_104_ = lean_st_ref_take(v___y_86_);
v_infoState_105_ = lean_ctor_get(v___x_104_, 8);
v_env_106_ = lean_ctor_get(v___x_104_, 0);
v_nextMacroScope_107_ = lean_ctor_get(v___x_104_, 1);
v_ngen_108_ = lean_ctor_get(v___x_104_, 2);
v_auxDeclNGen_109_ = lean_ctor_get(v___x_104_, 3);
v_traceState_110_ = lean_ctor_get(v___x_104_, 4);
v_cache_111_ = lean_ctor_get(v___x_104_, 5);
v_recordedDeps_112_ = lean_ctor_get(v___x_104_, 6);
v_messages_113_ = lean_ctor_get(v___x_104_, 7);
v_snapshotTasks_114_ = lean_ctor_get(v___x_104_, 9);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_138_ == 0)
{
v___x_116_ = v___x_104_;
v_isShared_117_ = v_isSharedCheck_138_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_snapshotTasks_114_);
lean_inc(v_infoState_105_);
lean_inc(v_messages_113_);
lean_inc(v_recordedDeps_112_);
lean_inc(v_cache_111_);
lean_inc(v_traceState_110_);
lean_inc(v_auxDeclNGen_109_);
lean_inc(v_ngen_108_);
lean_inc(v_nextMacroScope_107_);
lean_inc(v_env_106_);
lean_dec(v___x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_138_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v_enabled_118_; lean_object* v_assignment_119_; lean_object* v_lazyAssignment_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_136_; 
v_enabled_118_ = lean_ctor_get_uint8(v_infoState_105_, sizeof(void*)*3);
v_assignment_119_ = lean_ctor_get(v_infoState_105_, 0);
v_lazyAssignment_120_ = lean_ctor_get(v_infoState_105_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_infoState_105_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_infoState_105_, 2);
lean_dec(v_unused_137_);
v___x_122_ = v_infoState_105_;
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_lazyAssignment_120_);
lean_inc(v_assignment_119_);
lean_dec(v_infoState_105_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_124_ = lean_box(0);
v___x_125_ = l_Lean_PersistentArray_push___redArg(v_a_93_, v_a_100_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 2, v___x_125_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_assignment_119_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_lazyAssignment_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v___x_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_135_, sizeof(void*)*3, v_enabled_118_);
v___x_127_ = v_reuseFailAlloc_135_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 8, v___x_127_);
v___x_129_ = v___x_116_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_env_106_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_nextMacroScope_107_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_ngen_108_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_auxDeclNGen_109_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_traceState_110_);
lean_ctor_set(v_reuseFailAlloc_134_, 5, v_cache_111_);
lean_ctor_set(v_reuseFailAlloc_134_, 6, v_recordedDeps_112_);
lean_ctor_set(v_reuseFailAlloc_134_, 7, v_messages_113_);
lean_ctor_set(v_reuseFailAlloc_134_, 8, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 9, v_snapshotTasks_114_);
v___x_129_ = v_reuseFailAlloc_134_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_st_ref_put(v___y_86_, v___x_129_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_124_);
v___x_132_ = v___x_102_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_124_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v_a_93_);
v_a_140_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_99_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_99_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_86_ = stack[0].m_obj;
lean_object* v_mkInfoTree_87_ = stack[1].m_obj;
lean_object* v___y_88_ = stack[2].m_obj;
lean_object* v___y_89_ = stack[3].m_obj;
lean_object* v___y_90_ = stack[4].m_obj;
lean_object* v___y_91_ = stack[5].m_obj;
lean_object* v___y_92_ = stack[6].m_obj;
lean_object* v_a_93_ = stack[7].m_obj;
lean_object* v_a_x3f_94_ = stack[8].m_obj;
lean_object* v_res_148_;
v_res_148_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_86_, v_mkInfoTree_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v_a_93_, v_a_x3f_94_);
stack->m_obj
 = v_res_148_;
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
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_infoState_172_; lean_object* v_trees_173_; lean_object* v___x_174_; lean_object* v_infoState_175_; lean_object* v_env_176_; lean_object* v_nextMacroScope_177_; lean_object* v_ngen_178_; lean_object* v_auxDeclNGen_179_; lean_object* v_traceState_180_; lean_object* v_cache_181_; lean_object* v_recordedDeps_182_; lean_object* v_messages_183_; lean_object* v_snapshotTasks_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_205_; 
v___x_171_ = lean_st_ref_get(v___y_169_);
v_infoState_172_ = lean_ctor_get(v___x_171_, 8);
lean_inc_ref(v_infoState_172_);
lean_dec(v___x_171_);
v_trees_173_ = lean_ctor_get(v_infoState_172_, 2);
lean_inc_ref(v_trees_173_);
lean_dec_ref(v_infoState_172_);
v___x_174_ = lean_st_ref_take(v___y_169_);
v_infoState_175_ = lean_ctor_get(v___x_174_, 8);
v_env_176_ = lean_ctor_get(v___x_174_, 0);
v_nextMacroScope_177_ = lean_ctor_get(v___x_174_, 1);
v_ngen_178_ = lean_ctor_get(v___x_174_, 2);
v_auxDeclNGen_179_ = lean_ctor_get(v___x_174_, 3);
v_traceState_180_ = lean_ctor_get(v___x_174_, 4);
v_cache_181_ = lean_ctor_get(v___x_174_, 5);
v_recordedDeps_182_ = lean_ctor_get(v___x_174_, 6);
v_messages_183_ = lean_ctor_get(v___x_174_, 7);
v_snapshotTasks_184_ = lean_ctor_get(v___x_174_, 9);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_205_ == 0)
{
v___x_186_ = v___x_174_;
v_isShared_187_ = v_isSharedCheck_205_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snapshotTasks_184_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_183_);
lean_inc(v_recordedDeps_182_);
lean_inc(v_cache_181_);
lean_inc(v_traceState_180_);
lean_inc(v_auxDeclNGen_179_);
lean_inc(v_ngen_178_);
lean_inc(v_nextMacroScope_177_);
lean_inc(v_env_176_);
lean_dec(v___x_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_205_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
uint8_t v_enabled_188_; lean_object* v_assignment_189_; lean_object* v_lazyAssignment_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_203_; 
v_enabled_188_ = lean_ctor_get_uint8(v_infoState_175_, sizeof(void*)*3);
v_assignment_189_ = lean_ctor_get(v_infoState_175_, 0);
v_lazyAssignment_190_ = lean_ctor_get(v_infoState_175_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_infoState_175_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_infoState_175_, 2);
lean_dec(v_unused_204_);
v___x_192_ = v_infoState_175_;
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_lazyAssignment_190_);
lean_inc(v_assignment_189_);
lean_dec(v_infoState_175_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 2, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_assignment_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_lazyAssignment_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___x_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*3, v_enabled_188_);
v___x_196_ = v_reuseFailAlloc_202_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 8, v___x_196_);
v___x_198_ = v___x_186_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_env_176_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_nextMacroScope_177_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_ngen_178_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_auxDeclNGen_179_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_traceState_180_);
lean_ctor_set(v_reuseFailAlloc_201_, 5, v_cache_181_);
lean_ctor_set(v_reuseFailAlloc_201_, 6, v_recordedDeps_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 7, v_messages_183_);
lean_ctor_set(v_reuseFailAlloc_201_, 8, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_201_, 9, v_snapshotTasks_184_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_st_ref_put(v___y_169_, v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v_trees_173_);
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_169_ = stack[0].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_169_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_207_);
lean_dec(v___y_207_);
return v_res_209_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(lean_object* v_x_210_, lean_object* v_mkInfoTree_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_infoState_220_; uint8_t v_enabled_221_; 
v___x_219_ = lean_st_ref_get(v___y_217_);
v_infoState_220_ = lean_ctor_get(v___x_219_, 8);
lean_inc_ref(v_infoState_220_);
lean_dec(v___x_219_);
v_enabled_221_ = lean_ctor_get_uint8(v_infoState_220_, sizeof(void*)*3);
lean_dec_ref(v_infoState_220_);
if (v_enabled_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v_mkInfoTree_211_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
v___x_222_ = lean_apply_7(v_x_210_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, lean_box(0));
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_a_224_; lean_object* v_r_225_; 
v___x_223_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_217_);
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref(v___x_223_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
v_r_225_ = lean_apply_7(v_x_210_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, lean_box(0));
if (lean_obj_tag(v_r_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_a_226_ = lean_ctor_get(v_r_225_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_r_225_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_r_225_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v_r_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
lean_inc(v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 1);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_249_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_217_, v_mkInfoTree_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v_a_224_, v___x_231_);
lean_dec_ref(v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v___x_232_, 0);
lean_dec(v_unused_240_);
v___x_234_ = v___x_232_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_dec(v___x_232_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_a_226_);
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_226_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_226_);
v_a_241_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_232_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_232_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_a_251_ = lean_ctor_get(v_r_225_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_r_225_, 1);
v___x_252_ = lean_box(0);
v___x_253_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___lam__0(v___y_217_, v_mkInfoTree_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v_a_224_, v___x_252_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v___x_253_, 0);
lean_dec(v_unused_261_);
v___x_255_ = v___x_253_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_dec(v___x_253_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 1);
lean_ctor_set(v___x_255_, 0, v_a_251_);
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_251_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_a_251_);
v_a_262_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_253_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_253_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_210_ = stack[0].m_obj;
lean_object* v_mkInfoTree_211_ = stack[1].m_obj;
lean_object* v___y_212_ = stack[2].m_obj;
lean_object* v___y_213_ = stack[3].m_obj;
lean_object* v___y_214_ = stack[4].m_obj;
lean_object* v___y_215_ = stack[5].m_obj;
lean_object* v___y_216_ = stack[6].m_obj;
lean_object* v___y_217_ = stack[7].m_obj;
lean_object* v_res_270_;
v_res_270_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_210_, v_mkInfoTree_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_271_, lean_object* v_mkInfoTree_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_271_, v_mkInfoTree_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_280_;
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(lean_object* v_stx_281_, lean_object* v_output_282_, lean_object* v_trees_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_lctx_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_lctx_291_ = lean_ctor_get(v___y_286_, 2);
lean_inc_ref(v_lctx_291_);
v___x_292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_292_, 0, v_lctx_291_);
lean_ctor_set(v___x_292_, 1, v_stx_281_);
lean_ctor_set(v___x_292_, 2, v_output_282_);
v___x_293_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_trees_283_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_281_ = stack[0].m_obj;
lean_object* v_output_282_ = stack[1].m_obj;
lean_object* v_trees_283_ = stack[2].m_obj;
lean_object* v___y_284_ = stack[3].m_obj;
lean_object* v___y_285_ = stack[4].m_obj;
lean_object* v___y_286_ = stack[5].m_obj;
lean_object* v___y_287_ = stack[6].m_obj;
lean_object* v___y_288_ = stack[7].m_obj;
lean_object* v___y_289_ = stack[8].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___lam__0(v_stx_281_, v_output_282_, v_trees_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
stack->m_obj
 = v_res_296_;
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
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(lean_object* v_stx_308_, lean_object* v_output_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
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
LEAN_EXPORT void l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_308_ = stack[0].m_obj;
lean_object* v_output_309_ = stack[1].m_obj;
lean_object* v_x_310_ = stack[2].m_obj;
lean_object* v___y_311_ = stack[3].m_obj;
lean_object* v___y_312_ = stack[4].m_obj;
lean_object* v___y_313_ = stack[5].m_obj;
lean_object* v___y_314_ = stack[6].m_obj;
lean_object* v___y_315_ = stack[7].m_obj;
lean_object* v___y_316_ = stack[8].m_obj;
lean_object* v_res_320_;
v_res_320_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_308_, v_output_309_, v_x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg___boxed(lean_object* v_stx_321_, lean_object* v_output_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_321_, v_output_322_, v_x_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_331_;
}
}
lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_beforeStx_332_, lean_object* v_afterStx_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_inc_ref(v___y_335_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_343_, 0, v_x_334_);
lean_closure_set(v___f_343_, 1, v___y_335_);
lean_inc(v_afterStx_333_);
lean_inc(v_beforeStx_332_);
v___x_344_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_344_, 0, lean_box(0));
lean_closure_set(v___x_344_, 1, v_beforeStx_332_);
lean_closure_set(v___x_344_, 2, v_afterStx_333_);
lean_closure_set(v___x_344_, 3, v___f_343_);
v___x_345_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_beforeStx_332_, v_afterStx_333_, v___x_344_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_345_) == 0)
{
return v___x_345_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_beforeStx_332_ = stack[0].m_obj;
lean_object* v_afterStx_333_ = stack[1].m_obj;
lean_object* v_x_334_ = stack[2].m_obj;
lean_object* v___y_335_ = stack[3].m_obj;
lean_object* v___y_336_ = stack[4].m_obj;
lean_object* v___y_337_ = stack[5].m_obj;
lean_object* v___y_338_ = stack[6].m_obj;
lean_object* v___y_339_ = stack[7].m_obj;
lean_object* v___y_340_ = stack[8].m_obj;
lean_object* v___y_341_ = stack[9].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_332_, v_afterStx_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_beforeStx_355_, lean_object* v_afterStx_356_, lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_355_, v_afterStx_356_, v_x_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__26(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Array_mkArray0___redArg();
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoRepeat___closed__32(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__31));
v___x_438_ = l_String_toRawSubstring_x27(v___x_437_);
return v___x_438_;
}
}
lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_471_, lean_object* v_dec_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v_expanded_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; 
v___x_481_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
lean_inc(v_stx_471_);
v___x_482_ = l_Lean_Syntax_isOfKind(v_stx_471_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v___x_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v_tk_588_; lean_object* v___y_590_; lean_object* v_var_x3f_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___x_642_; lean_object* v_inv_x3f_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v_tk_588_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_564_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_662_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_642_);
v___x_663_ = l_Lean_Syntax_isNone(v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
lean_inc(v___x_662_);
v___x_664_ = l_Lean_Syntax_matchesNull(v___x_662_, v___x_642_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v___x_662_);
lean_dec(v_tk_588_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v___x_665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_665_;
}
else
{
lean_object* v_inv_x3f_666_; 
v_inv_x3f_666_ = l_Lean_Syntax_getArg(v___x_662_, v___x_564_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_666_);
v___x_670_ = l_Lean_Syntax_isOfKind(v_inv_x3f_666_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v_inv_x3f_666_);
lean_dec(v_tk_588_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v___x_671_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_671_;
}
else
{
goto v___jp_667_;
}
}
else
{
goto v___jp_667_;
}
v___jp_667_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_inv_x3f_666_);
v_inv_x3f_644_ = v___x_668_;
v___y_645_ = v_a_473_;
v___y_646_ = v_a_474_;
v___y_647_ = v_a_475_;
v___y_648_ = v_a_476_;
v___y_649_ = v_a_477_;
v___y_650_ = v_a_478_;
v___y_651_ = v_a_479_;
goto v___jp_643_;
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_662_);
v___x_672_ = lean_box(0);
v_inv_x3f_644_ = v___x_672_;
v___y_645_ = v_a_473_;
v___y_646_ = v_a_474_;
v___y_647_ = v_a_475_;
v___y_648_ = v_a_476_;
v___y_649_ = v_a_477_;
v___y_650_ = v_a_478_;
v___y_651_ = v_a_479_;
goto v___jp_643_;
}
v___jp_565_:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc_ref(v___y_575_);
v___x_583_ = l_Array_append___redArg(v___y_575_, v___y_582_);
lean_dec_ref(v___y_582_);
lean_inc(v___y_571_);
lean_inc(v___y_580_);
v___x_584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_584_, 0, v___y_580_);
lean_ctor_set(v___x_584_, 1, v___y_571_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
if (lean_obj_tag(v___y_581_) == 1)
{
lean_object* v_val_585_; lean_object* v___x_586_; 
v_val_585_ = lean_ctor_get(v___y_581_, 0);
lean_inc(v_val_585_);
lean_dec_ref_known(v___y_581_, 1);
v___x_586_ = l_Array_mkArray1___redArg(v_val_585_);
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___x_584_;
v___y_501_ = v___y_570_;
v___y_502_ = v___y_571_;
v___y_503_ = v___y_572_;
v___y_504_ = v___y_573_;
v___y_505_ = v___y_574_;
v___y_506_ = v___y_575_;
v___y_507_ = v___y_577_;
v___y_508_ = v___y_576_;
v___y_509_ = v___y_578_;
v___y_510_ = v___y_580_;
v___y_511_ = v___y_579_;
v___y_512_ = v___x_586_;
goto v___jp_495_;
}
else
{
lean_object* v___x_587_; 
lean_dec(v___y_581_);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_496_ = v___y_566_;
v___y_497_ = v___y_567_;
v___y_498_ = v___y_568_;
v___y_499_ = v___y_569_;
v___y_500_ = v___x_584_;
v___y_501_ = v___y_570_;
v___y_502_ = v___y_571_;
v___y_503_ = v___y_572_;
v___y_504_ = v___y_573_;
v___y_505_ = v___y_574_;
v___y_506_ = v___y_575_;
v___y_507_ = v___y_577_;
v___y_508_ = v___y_576_;
v___y_509_ = v___y_578_;
v___y_510_ = v___y_580_;
v___y_511_ = v___y_579_;
v___y_512_ = v___x_587_;
goto v___jp_495_;
}
}
v___jp_589_:
{
lean_object* v_toCold_599_; lean_object* v_ref_600_; lean_object* v_quotContext_601_; lean_object* v_currMacroScope_602_; lean_object* v___x_603_; lean_object* v_seq_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_toCold_599_ = lean_ctor_get(v___y_597_, 0);
v_ref_600_ = lean_ctor_get(v___y_597_, 2);
v_quotContext_601_ = lean_ctor_get(v_toCold_599_, 8);
v_currMacroScope_602_ = lean_ctor_get(v_toCold_599_, 9);
v___x_603_ = lean_unsigned_to_nat(3u);
v_seq_604_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_603_);
v___x_605_ = 0;
v___x_606_ = l_Lean_SourceInfo_fromRef(v_ref_600_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__20));
v___x_608_ = l_Lean_SourceInfo_fromRef(v_tk_588_, v___x_482_);
lean_dec(v_tk_588_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__21));
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_612_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__25));
v___x_613_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
lean_inc_n(v___x_606_, 7);
v___x_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_606_);
lean_ctor_set(v___x_614_, 1, v___x_611_);
lean_ctor_set(v___x_614_, 2, v___x_613_);
v___x_615_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__28));
v___x_616_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__29));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_606_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_Syntax_node1(v___x_606_, v___x_615_, v___x_617_);
v___x_619_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__30));
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_606_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__32, &l_Lean_Elab_Do_elabDoRepeat___closed__32_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__32);
v___x_622_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__35));
lean_inc(v_currMacroScope_602_);
lean_inc(v_quotContext_601_);
v___x_623_ = l_Lean_addMacroScope(v_quotContext_601_, v___x_622_, v_currMacroScope_602_);
v___x_624_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__40));
v___x_625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_606_);
lean_ctor_set(v___x_625_, 1, v___x_621_);
lean_ctor_set(v___x_625_, 2, v___x_623_);
lean_ctor_set(v___x_625_, 3, v___x_624_);
v___x_626_ = l_Lean_Syntax_node4(v___x_606_, v___x_612_, v___x_614_, v___x_618_, v___x_620_, v___x_625_);
v___x_627_ = l_Lean_Syntax_node1(v___x_606_, v___x_611_, v___x_626_);
if (lean_obj_tag(v___y_590_) == 1)
{
lean_object* v_val_628_; lean_object* v___x_629_; 
v_val_628_ = lean_ctor_get(v___y_590_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v___y_590_, 1);
v___x_629_ = l_Array_mkArray1___redArg(v_val_628_);
v___y_566_ = v___x_607_;
v___y_567_ = v___y_596_;
v___y_568_ = v___x_610_;
v___y_569_ = v___y_592_;
v___y_570_ = v___y_597_;
v___y_571_ = v___x_611_;
v___y_572_ = v___y_593_;
v___y_573_ = v___y_598_;
v___y_574_ = v___y_594_;
v___y_575_ = v___x_613_;
v___y_576_ = v___y_595_;
v___y_577_ = v_seq_604_;
v___y_578_ = v_ref_600_;
v___y_579_ = v___x_627_;
v___y_580_ = v___x_606_;
v___y_581_ = v_var_x3f_591_;
v___y_582_ = v___x_629_;
goto v___jp_565_;
}
else
{
lean_object* v___x_630_; 
lean_dec(v___y_590_);
v___x_630_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_566_ = v___x_607_;
v___y_567_ = v___y_596_;
v___y_568_ = v___x_610_;
v___y_569_ = v___y_592_;
v___y_570_ = v___y_597_;
v___y_571_ = v___x_611_;
v___y_572_ = v___y_593_;
v___y_573_ = v___y_598_;
v___y_574_ = v___y_594_;
v___y_575_ = v___x_613_;
v___y_576_ = v___y_595_;
v___y_577_ = v_seq_604_;
v___y_578_ = v_ref_600_;
v___y_579_ = v___x_627_;
v___y_580_ = v___x_606_;
v___y_581_ = v_var_x3f_591_;
v___y_582_ = v___x_630_;
goto v___jp_565_;
}
}
v___jp_631_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___y_635_);
v___y_590_ = v___y_634_;
v_var_x3f_591_ = v___x_641_;
v___y_592_ = v___y_640_;
v___y_593_ = v___y_639_;
v___y_594_ = v___y_633_;
v___y_595_ = v___y_636_;
v___y_596_ = v___y_638_;
v___y_597_ = v___y_637_;
v___y_598_ = v___y_632_;
goto v___jp_589_;
}
v___jp_643_:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_unsigned_to_nat(2u);
v___x_653_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_652_);
v___x_654_ = l_Lean_Syntax_isNone(v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
lean_inc(v___x_653_);
v___x_655_ = l_Lean_Syntax_matchesNull(v___x_653_, v___x_642_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v___x_653_);
lean_dec(v_inv_x3f_644_);
lean_dec(v_tk_588_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v___x_656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_656_;
}
else
{
lean_object* v_var_x3f_657_; 
v_var_x3f_657_ = l_Lean_Syntax_getArg(v___x_653_, v___x_564_);
lean_dec(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_var_x3f_657_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_var_x3f_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v_var_x3f_657_);
lean_dec(v_inv_x3f_644_);
lean_dec(v_tk_588_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v___x_660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_660_;
}
else
{
v___y_632_ = v___y_651_;
v___y_633_ = v___y_647_;
v___y_634_ = v_inv_x3f_644_;
v___y_635_ = v_var_x3f_657_;
v___y_636_ = v___y_648_;
v___y_637_ = v___y_650_;
v___y_638_ = v___y_649_;
v___y_639_ = v___y_646_;
v___y_640_ = v___y_645_;
goto v___jp_631_;
}
}
else
{
v___y_632_ = v___y_651_;
v___y_633_ = v___y_647_;
v___y_634_ = v_inv_x3f_644_;
v___y_635_ = v_var_x3f_657_;
v___y_636_ = v___y_648_;
v___y_637_ = v___y_650_;
v___y_638_ = v___y_649_;
v___y_639_ = v___y_646_;
v___y_640_ = v___y_645_;
goto v___jp_631_;
}
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v___x_653_);
v___x_661_ = lean_box(0);
v___y_590_ = v_inv_x3f_644_;
v_var_x3f_591_ = v___x_661_;
v___y_592_ = v___y_645_;
v___y_593_ = v___y_646_;
v___y_594_ = v___y_647_;
v___y_595_ = v___y_648_;
v___y_596_ = v___y_649_;
v___y_597_ = v___y_650_;
v___y_598_ = v___y_651_;
goto v___jp_589_;
}
}
}
v___jp_483_:
{
lean_object* v___x_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(v___x_482_);
lean_inc(v_expanded_484_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 11, 3);
lean_closure_set(v___f_493_, 0, v_expanded_484_);
lean_closure_set(v___f_493_, 1, v_dec_472_);
lean_closure_set(v___f_493_, 2, v___x_492_);
v___x_494_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_stx_471_, v_expanded_484_, v___f_493_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_494_;
}
v___jp_495_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_inc_ref(v___y_506_);
v___x_513_ = l_Array_append___redArg(v___y_506_, v___y_512_);
lean_dec_ref(v___y_512_);
lean_inc(v___y_502_);
lean_inc_n(v___y_510_, 2);
v___x_514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_514_, 0, v___y_510_);
lean_ctor_set(v___x_514_, 1, v___y_502_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
v___x_515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v___y_510_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
lean_inc(v___y_507_);
lean_inc(v___y_496_);
v___x_517_ = l_Lean_Syntax_node6(v___y_510_, v___y_496_, v___y_498_, v___y_511_, v___y_500_, v___x_514_, v___x_516_, v___y_507_);
v___x_518_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_507_, v___y_503_, v___y_505_, v___y_508_, v___y_497_, v___y_501_, v___y_504_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; uint8_t v_breaks_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_breaks_520_ = lean_ctor_get_uint8(v_a_519_, sizeof(void*)*2);
lean_dec(v_a_519_);
if (v_breaks_520_ == 0)
{
if (v___x_482_ == 0)
{
lean_dec(v___y_502_);
v_expanded_484_ = v___x_517_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_503_;
v___y_487_ = v___y_505_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_501_;
v___y_491_ = v___y_504_;
goto v___jp_483_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_499_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_resultType_523_; lean_object* v___x_524_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v_resultType_523_ = lean_ctor_get(v_dec_472_, 1);
lean_inc_ref(v_resultType_523_);
v___x_524_ = l_Lean_Meta_isExprDefEqGuarded(v_resultType_523_, v_a_522_, v___y_508_, v___y_497_, v___y_501_, v___y_504_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; uint8_t v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_unbox(v_a_525_);
lean_dec(v_a_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_527_ = l_Lean_SourceInfo_fromRef(v___y_509_, v_breaks_520_);
v___x_528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
lean_inc_n(v___x_527_, 11);
v___x_529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_515_);
v___x_530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_531_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_532_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__12));
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_527_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_inc_n(v___y_502_, 2);
v___x_534_ = l_Lean_Syntax_node1(v___x_527_, v___y_502_, v___x_533_);
v___x_535_ = l_Lean_Syntax_node2(v___x_527_, v___x_531_, v___x_517_, v___x_534_);
v___x_536_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__14));
v___x_537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__16));
v___x_538_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__17));
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_527_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_Syntax_node1(v___x_527_, v___x_537_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node1(v___x_527_, v___x_536_, v___x_540_);
lean_inc_ref(v___y_506_);
v___x_542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_542_, 0, v___x_527_);
lean_ctor_set(v___x_542_, 1, v___y_502_);
lean_ctor_set(v___x_542_, 2, v___y_506_);
v___x_543_ = l_Lean_Syntax_node2(v___x_527_, v___x_531_, v___x_541_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node2(v___x_527_, v___y_502_, v___x_535_, v___x_543_);
v___x_545_ = l_Lean_Syntax_node1(v___x_527_, v___x_530_, v___x_544_);
v___x_546_ = l_Lean_Syntax_node2(v___x_527_, v___x_528_, v___x_529_, v___x_545_);
v_expanded_484_ = v___x_546_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_503_;
v___y_487_ = v___y_505_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_501_;
v___y_491_ = v___y_504_;
goto v___jp_483_;
}
else
{
lean_dec(v___y_502_);
v_expanded_484_ = v___x_517_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_503_;
v___y_487_ = v___y_505_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_501_;
v___y_491_ = v___y_504_;
goto v___jp_483_;
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___x_517_);
lean_dec(v___y_502_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v_a_547_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_524_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_524_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_dec(v___x_517_);
lean_dec(v___y_502_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
return v___x_521_;
}
}
}
else
{
lean_dec(v___y_502_);
v_expanded_484_ = v___x_517_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_503_;
v___y_487_ = v___y_505_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_501_;
v___y_491_ = v___y_504_;
goto v___jp_483_;
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v___x_517_);
lean_dec(v___y_502_);
lean_dec_ref(v_dec_472_);
lean_dec(v_stx_471_);
v_a_555_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_518_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_518_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoRepeat_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_471_ = stack[0].m_obj;
lean_object* v_dec_472_ = stack[1].m_obj;
lean_object* v_a_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_a_475_ = stack[4].m_obj;
lean_object* v_a_476_ = stack[5].m_obj;
lean_object* v_a_477_ = stack[6].m_obj;
lean_object* v_a_478_ = stack[7].m_obj;
lean_object* v_a_479_ = stack[8].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_471_, v_dec_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_674_, lean_object* v_dec_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_674_, v_dec_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_684_;
}
}
lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_685_, lean_object* v_beforeStx_686_, lean_object* v_afterStx_687_, lean_object* v_x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_beforeStx_686_, v_afterStx_687_, v_x_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_beforeStx_686_ = stack[1].m_obj;
lean_object* v_afterStx_687_ = stack[2].m_obj;
lean_object* v_x_688_ = stack[3].m_obj;
lean_object* v___y_689_ = stack[4].m_obj;
lean_object* v___y_690_ = stack[5].m_obj;
lean_object* v___y_691_ = stack[6].m_obj;
lean_object* v___y_692_ = stack[7].m_obj;
lean_object* v___y_693_ = stack[8].m_obj;
lean_object* v___y_694_ = stack[9].m_obj;
lean_object* v___y_695_ = stack[10].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_box(0), v_beforeStx_686_, v_afterStx_687_, v_x_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_699_, lean_object* v_beforeStx_700_, lean_object* v_afterStx_701_, lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_699_, v_beforeStx_700_, v_afterStx_701_, v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_711_;
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_object* v_00_u03b1_712_, lean_object* v_stx_713_, lean_object* v_output_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___redArg(v_stx_713_, v_output_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT void l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_713_ = stack[1].m_obj;
lean_object* v_output_714_ = stack[2].m_obj;
lean_object* v_x_715_ = stack[3].m_obj;
lean_object* v___y_716_ = stack[4].m_obj;
lean_object* v___y_717_ = stack[5].m_obj;
lean_object* v___y_718_ = stack[6].m_obj;
lean_object* v___y_719_ = stack[7].m_obj;
lean_object* v___y_720_ = stack[8].m_obj;
lean_object* v___y_721_ = stack[9].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(lean_box(0), v_stx_713_, v_output_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1___boxed(lean_object* v_00_u03b1_725_, lean_object* v_stx_726_, lean_object* v_output_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1(v_00_u03b1_725_, v_stx_726_, v_output_727_, v_x_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_736_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___redArg(v___y_742_);
return v___x_744_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_737_ = stack[0].m_obj;
lean_object* v___y_738_ = stack[1].m_obj;
lean_object* v___y_739_ = stack[2].m_obj;
lean_object* v___y_740_ = stack[3].m_obj;
lean_object* v___y_741_ = stack[4].m_obj;
lean_object* v___y_742_ = stack[5].m_obj;
lean_object* v_res_745_;
v_res_745_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_spec__3(v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_753_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_754_, lean_object* v_x_755_, lean_object* v_mkInfoTree_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___redArg(v_x_755_, v_mkInfoTree_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_755_ = stack[1].m_obj;
lean_object* v_mkInfoTree_756_ = stack[2].m_obj;
lean_object* v___y_757_ = stack[3].m_obj;
lean_object* v___y_758_ = stack[4].m_obj;
lean_object* v___y_759_ = stack[5].m_obj;
lean_object* v___y_760_ = stack[6].m_obj;
lean_object* v___y_761_ = stack[7].m_obj;
lean_object* v___y_762_ = stack[8].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(lean_box(0), v_x_755_, v_mkInfoTree_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_766_, lean_object* v_x_767_, lean_object* v_mkInfoTree_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoRepeat_spec__1_spec__1_spec__2(v_00_u03b1_766_, v_x_767_, v_mkInfoTree_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_776_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_786_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_787_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_788_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_789_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_790_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_786_, v___x_787_, v___x_788_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_791_;
v_res_791_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_793_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3(){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___closed__0));
v___x_798_ = l_Lean_addBuiltinDocString(v___x_796_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_799_;
v_res_799_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3___boxed(lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat_docString__3();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile(lean_object* v_x_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
lean_inc(v_x_825_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_x_825_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v_x_825_);
v___x_830_ = l_Lean_Macro_throwUnsupported___redArg(v_a_827_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v_tk_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_887_; lean_object* v_dec_x3f_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_inv_x3f_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v_tk_832_ = l_Lean_Syntax_getArg(v_x_825_, v___x_831_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = l_Lean_Syntax_getArg(v_x_825_, v___x_833_);
v___x_925_ = lean_unsigned_to_nat(2u);
v___x_926_ = l_Lean_Syntax_getArg(v_x_825_, v___x_925_);
v___x_927_ = l_Lean_Syntax_isNone(v___x_926_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
lean_inc(v___x_926_);
v___x_928_ = l_Lean_Syntax_matchesNull(v___x_926_, v___x_833_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec(v___x_926_);
lean_dec(v___x_834_);
lean_dec(v_tk_832_);
lean_dec(v_x_825_);
v___x_929_ = l_Lean_Macro_throwUnsupported___redArg(v_a_827_);
return v___x_929_;
}
else
{
lean_object* v_inv_x3f_930_; 
v_inv_x3f_930_ = l_Lean_Syntax_getArg(v___x_926_, v___x_831_);
lean_dec(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_930_);
v___x_934_ = l_Lean_Syntax_isOfKind(v_inv_x3f_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v_inv_x3f_930_);
lean_dec(v___x_834_);
lean_dec(v_tk_832_);
lean_dec(v_x_825_);
v___x_935_ = l_Lean_Macro_throwUnsupported___redArg(v_a_827_);
return v___x_935_;
}
else
{
goto v___jp_931_;
}
}
else
{
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v_inv_x3f_930_);
v_inv_x3f_912_ = v___x_932_;
v___y_913_ = v_a_826_;
v___y_914_ = v_a_827_;
goto v___jp_911_;
}
}
}
else
{
lean_object* v___x_936_; 
lean_dec(v___x_926_);
v___x_936_ = lean_box(0);
v_inv_x3f_912_ = v___x_936_;
v___y_913_ = v_a_826_;
v___y_914_ = v_a_827_;
goto v___jp_911_;
}
v___jp_835_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_inc_ref_n(v___y_836_, 2);
v___x_845_ = l_Array_append___redArg(v___y_836_, v___y_844_);
lean_dec_ref(v___y_844_);
lean_inc_n(v___y_839_, 5);
lean_inc_n(v___y_841_, 15);
v___x_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_846_, 0, v___y_841_);
lean_ctor_set(v___x_846_, 1, v___y_839_);
lean_ctor_set(v___x_846_, 2, v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_848_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_849_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_850_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_841_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_841_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_854_, 0, v___y_841_);
lean_ctor_set(v___x_854_, 1, v___y_839_);
lean_ctor_set(v___x_854_, 2, v___y_836_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__6));
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_841_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_858_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___y_841_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Lean_Syntax_node1(v___y_841_, v___x_857_, v___x_859_);
lean_inc_ref_n(v___x_854_, 2);
v___x_861_ = l_Lean_Syntax_node2(v___y_841_, v___x_848_, v___x_860_, v___x_854_);
v___x_862_ = l_Lean_Syntax_node1(v___y_841_, v___y_839_, v___x_861_);
v___x_863_ = l_Lean_Syntax_node1(v___y_841_, v___x_847_, v___x_862_);
v___x_864_ = l_Lean_Syntax_node2(v___y_841_, v___y_839_, v___x_856_, v___x_863_);
v___x_865_ = l_Lean_Syntax_node6(v___y_841_, v___x_849_, v___x_851_, v___x_834_, v___x_853_, v___y_838_, v___x_854_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node2(v___y_841_, v___x_848_, v___x_865_, v___x_854_);
v___x_867_ = l_Lean_Syntax_node1(v___y_841_, v___y_839_, v___x_866_);
v___x_868_ = l_Lean_Syntax_node1(v___y_841_, v___x_847_, v___x_867_);
lean_inc(v___y_843_);
v___x_869_ = l_Lean_Syntax_node4(v___y_841_, v___y_843_, v___y_837_, v___y_842_, v___x_846_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___y_840_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc_ref(v___y_872_);
v___x_881_ = l_Array_append___redArg(v___y_872_, v___y_880_);
lean_dec_ref(v___y_880_);
lean_inc(v___y_875_);
lean_inc(v___y_878_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v___y_878_);
lean_ctor_set(v___x_882_, 1, v___y_875_);
lean_ctor_set(v___x_882_, 2, v___x_881_);
if (lean_obj_tag(v___y_876_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_884_; 
v_val_883_ = lean_ctor_get(v___y_876_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___y_876_, 1);
v___x_884_ = l_Array_mkArray1___redArg(v_val_883_);
v___y_836_ = v___y_872_;
v___y_837_ = v___y_873_;
v___y_838_ = v___y_874_;
v___y_839_ = v___y_875_;
v___y_840_ = v___y_877_;
v___y_841_ = v___y_878_;
v___y_842_ = v___x_882_;
v___y_843_ = v___y_879_;
v___y_844_ = v___x_884_;
goto v___jp_835_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v___y_876_);
v___x_885_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_836_ = v___y_872_;
v___y_837_ = v___y_873_;
v___y_838_ = v___y_874_;
v___y_839_ = v___y_875_;
v___y_840_ = v___y_877_;
v___y_841_ = v___y_878_;
v___y_842_ = v___x_882_;
v___y_843_ = v___y_879_;
v___y_844_ = v___x_885_;
goto v___jp_835_;
}
}
v___jp_886_:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_ref_891_ = lean_ctor_get(v___y_889_, 5);
v___x_892_ = lean_unsigned_to_nat(5u);
v___x_893_ = l_Lean_Syntax_getArg(v_x_825_, v___x_892_);
lean_dec(v_x_825_);
v___x_894_ = 0;
v___x_895_ = l_Lean_SourceInfo_fromRef(v_ref_891_, v___x_894_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_897_ = l_Lean_SourceInfo_fromRef(v_tk_832_, v___x_829_);
lean_dec(v_tk_832_);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_901_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_887_) == 1)
{
lean_object* v_val_902_; lean_object* v___x_903_; 
v_val_902_ = lean_ctor_get(v___y_887_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v___y_887_, 1);
v___x_903_ = l_Array_mkArray1___redArg(v_val_902_);
v___y_872_ = v___x_901_;
v___y_873_ = v___x_899_;
v___y_874_ = v___x_893_;
v___y_875_ = v___x_900_;
v___y_876_ = v_dec_x3f_888_;
v___y_877_ = v___y_890_;
v___y_878_ = v___x_895_;
v___y_879_ = v___x_896_;
v___y_880_ = v___x_903_;
goto v___jp_871_;
}
else
{
lean_object* v___x_904_; 
lean_dec(v___y_887_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_872_ = v___x_901_;
v___y_873_ = v___x_899_;
v___y_874_ = v___x_893_;
v___y_875_ = v___x_900_;
v___y_876_ = v_dec_x3f_888_;
v___y_877_ = v___y_890_;
v___y_878_ = v___x_895_;
v___y_879_ = v___x_896_;
v___y_880_ = v___x_904_;
goto v___jp_871_;
}
}
v___jp_905_:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___y_906_);
v___y_887_ = v___y_907_;
v_dec_x3f_888_ = v___x_910_;
v___y_889_ = v___y_909_;
v___y_890_ = v___y_908_;
goto v___jp_886_;
}
v___jp_911_:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_unsigned_to_nat(3u);
v___x_916_ = l_Lean_Syntax_getArg(v_x_825_, v___x_915_);
v___x_917_ = l_Lean_Syntax_isNone(v___x_916_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
lean_inc(v___x_916_);
v___x_918_ = l_Lean_Syntax_matchesNull(v___x_916_, v___x_833_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_dec(v___x_916_);
lean_dec(v_inv_x3f_912_);
lean_dec(v___x_834_);
lean_dec(v_tk_832_);
lean_dec(v_x_825_);
v___x_919_ = l_Lean_Macro_throwUnsupported___redArg(v___y_914_);
return v___x_919_;
}
else
{
lean_object* v_dec_x3f_920_; 
v_dec_x3f_920_ = l_Lean_Syntax_getArg(v___x_916_, v___x_831_);
lean_dec(v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_920_);
v___x_922_ = l_Lean_Syntax_isOfKind(v_dec_x3f_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec(v_dec_x3f_920_);
lean_dec(v_inv_x3f_912_);
lean_dec(v___x_834_);
lean_dec(v_tk_832_);
lean_dec(v_x_825_);
v___x_923_ = l_Lean_Macro_throwUnsupported___redArg(v___y_914_);
return v___x_923_;
}
else
{
v___y_906_ = v_dec_x3f_920_;
v___y_907_ = v_inv_x3f_912_;
v___y_908_ = v___y_914_;
v___y_909_ = v___y_913_;
goto v___jp_905_;
}
}
else
{
v___y_906_ = v_dec_x3f_920_;
v___y_907_ = v_inv_x3f_912_;
v___y_908_ = v___y_914_;
v___y_909_ = v___y_913_;
goto v___jp_905_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_916_);
v___x_924_ = lean_box(0);
v___y_887_ = v_inv_x3f_912_;
v_dec_x3f_888_ = v___x_924_;
v___y_889_ = v___y_913_;
v___y_890_ = v___y_914_;
goto v___jp_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoWhile___boxed(lean_object* v_x_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Elab_Do_expandDoWhile(v_x_937_, v_a_938_, v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_940_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1(){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_948_ = l_Lean_Elab_macroAttribute;
v___x_949_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__1));
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___closed__1));
v___x_951_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoWhile___boxed), 3, 0);
v___x_952_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_948_, v___x_949_, v___x_950_, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_953_;
v_res_953_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1___boxed(lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoWhile___regBuiltin_Lean_Elab_Do_expandDoWhile__1();
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil(lean_object* v_x_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
lean_inc(v_x_968_);
v___x_1013_ = l_Lean_Syntax_isOfKind(v_x_968_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v_x_968_);
v___x_1014_ = l_Lean_Macro_throwUnsupported___redArg(v_a_970_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v_tk_1032_; lean_object* v___y_1034_; lean_object* v_dec_x3f_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___x_1060_; lean_object* v_inv_x3f_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v_tk_1032_ = l_Lean_Syntax_getArg(v_x_968_, v___x_1015_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1075_ = l_Lean_Syntax_getArg(v_x_968_, v___x_1060_);
v___x_1076_ = l_Lean_Syntax_isNone(v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; 
lean_inc(v___x_1075_);
v___x_1077_ = l_Lean_Syntax_matchesNull(v___x_1075_, v___x_1060_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec(v___x_1075_);
lean_dec(v_tk_1032_);
lean_dec(v_x_968_);
v___x_1078_ = l_Lean_Macro_throwUnsupported___redArg(v_a_970_);
return v___x_1078_;
}
else
{
lean_object* v_inv_x3f_1079_; 
v_inv_x3f_1079_ = l_Lean_Syntax_getArg(v___x_1075_, v___x_1015_);
lean_dec(v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__44));
lean_inc(v_inv_x3f_1079_);
v___x_1083_ = l_Lean_Syntax_isOfKind(v_inv_x3f_1079_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_inv_x3f_1079_);
lean_dec(v_tk_1032_);
lean_dec(v_x_968_);
v___x_1084_ = l_Lean_Macro_throwUnsupported___redArg(v_a_970_);
return v___x_1084_;
}
else
{
goto v___jp_1080_;
}
}
else
{
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_inv_x3f_1079_);
v_inv_x3f_1062_ = v___x_1081_;
v___y_1063_ = v_a_969_;
v___y_1064_ = v_a_970_;
goto v___jp_1061_;
}
}
}
else
{
lean_object* v___x_1085_; 
lean_dec(v___x_1075_);
v___x_1085_ = lean_box(0);
v_inv_x3f_1062_ = v___x_1085_;
v___y_1063_ = v_a_969_;
v___y_1064_ = v_a_970_;
goto v___jp_1061_;
}
v___jp_1016_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_inc_ref(v___y_1019_);
v___x_1027_ = l_Array_append___redArg(v___y_1019_, v___y_1026_);
lean_dec_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc(v___y_1023_);
v___x_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1023_);
lean_ctor_set(v___x_1028_, 1, v___y_1025_);
lean_ctor_set(v___x_1028_, 2, v___x_1027_);
if (lean_obj_tag(v___y_1020_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1030_; 
v_val_1029_ = lean_ctor_get(v___y_1020_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___y_1020_, 1);
v___x_1030_ = l_Array_mkArray1___redArg(v_val_1029_);
v___y_972_ = v___y_1017_;
v___y_973_ = v___y_1018_;
v___y_974_ = v___y_1019_;
v___y_975_ = v___y_1021_;
v___y_976_ = v___y_1022_;
v___y_977_ = v___x_1028_;
v___y_978_ = v___y_1023_;
v___y_979_ = v___y_1024_;
v___y_980_ = v___y_1025_;
v___y_981_ = v___x_1030_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1031_; 
lean_dec(v___y_1020_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_972_ = v___y_1017_;
v___y_973_ = v___y_1018_;
v___y_974_ = v___y_1019_;
v___y_975_ = v___y_1021_;
v___y_976_ = v___y_1022_;
v___y_977_ = v___x_1028_;
v___y_978_ = v___y_1023_;
v___y_979_ = v___y_1024_;
v___y_980_ = v___y_1025_;
v___y_981_ = v___x_1031_;
goto v___jp_971_;
}
}
v___jp_1033_:
{
lean_object* v_ref_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_ref_1038_ = lean_ctor_get(v___y_1036_, 5);
v___x_1039_ = lean_unsigned_to_nat(3u);
v___x_1040_ = l_Lean_Syntax_getArg(v_x_968_, v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(5u);
v___x_1042_ = l_Lean_Syntax_getArg(v_x_968_, v___x_1041_);
lean_dec(v_x_968_);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_SourceInfo_fromRef(v_ref_1038_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1046_ = l_Lean_SourceInfo_fromRef(v_tk_1032_, v___x_1013_);
lean_dec(v_tk_1032_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__10));
v___x_1048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__23));
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Do_elabDoRepeat___closed__26, &l_Lean_Elab_Do_elabDoRepeat___closed__26_once, _init_l_Lean_Elab_Do_elabDoRepeat___closed__26);
if (lean_obj_tag(v___y_1034_) == 1)
{
lean_object* v_val_1051_; lean_object* v___x_1052_; 
v_val_1051_ = lean_ctor_get(v___y_1034_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v___y_1034_, 1);
v___x_1052_ = l_Array_mkArray1___redArg(v_val_1051_);
v___y_1017_ = v___x_1040_;
v___y_1018_ = v___x_1048_;
v___y_1019_ = v___x_1050_;
v___y_1020_ = v_dec_x3f_1035_;
v___y_1021_ = v___y_1037_;
v___y_1022_ = v___x_1045_;
v___y_1023_ = v___x_1044_;
v___y_1024_ = v___x_1042_;
v___y_1025_ = v___x_1049_;
v___y_1026_ = v___x_1052_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1053_; 
lean_dec(v___y_1034_);
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__18));
v___y_1017_ = v___x_1040_;
v___y_1018_ = v___x_1048_;
v___y_1019_ = v___x_1050_;
v___y_1020_ = v_dec_x3f_1035_;
v___y_1021_ = v___y_1037_;
v___y_1022_ = v___x_1045_;
v___y_1023_ = v___x_1044_;
v___y_1024_ = v___x_1042_;
v___y_1025_ = v___x_1049_;
v___y_1026_ = v___x_1053_;
goto v___jp_1016_;
}
}
v___jp_1054_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1055_);
v___y_1034_ = v___y_1056_;
v_dec_x3f_1035_ = v___x_1059_;
v___y_1036_ = v___y_1058_;
v___y_1037_ = v___y_1057_;
goto v___jp_1033_;
}
v___jp_1061_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_unsigned_to_nat(2u);
v___x_1066_ = l_Lean_Syntax_getArg(v_x_968_, v___x_1065_);
v___x_1067_ = l_Lean_Syntax_isNone(v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; 
lean_inc(v___x_1066_);
v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1066_, v___x_1060_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v___x_1066_);
lean_dec(v_inv_x3f_1062_);
lean_dec(v_tk_1032_);
lean_dec(v_x_968_);
v___x_1069_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1064_);
return v___x_1069_;
}
else
{
lean_object* v_dec_x3f_1070_; 
v_dec_x3f_1070_ = l_Lean_Syntax_getArg(v___x_1066_, v___x_1015_);
lean_dec(v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__42));
lean_inc(v_dec_x3f_1070_);
v___x_1072_ = l_Lean_Syntax_isOfKind(v_dec_x3f_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_dec_x3f_1070_);
lean_dec(v_inv_x3f_1062_);
lean_dec(v_tk_1032_);
lean_dec(v_x_968_);
v___x_1073_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1064_);
return v___x_1073_;
}
else
{
v___y_1055_ = v_dec_x3f_1070_;
v___y_1056_ = v_inv_x3f_1062_;
v___y_1057_ = v___y_1064_;
v___y_1058_ = v___y_1063_;
goto v___jp_1054_;
}
}
else
{
v___y_1055_ = v_dec_x3f_1070_;
v___y_1056_ = v_inv_x3f_1062_;
v___y_1057_ = v___y_1064_;
v___y_1058_ = v___y_1063_;
goto v___jp_1054_;
}
}
}
else
{
lean_object* v___x_1074_; 
lean_dec(v___x_1066_);
v___x_1074_ = lean_box(0);
v___y_1034_ = v_inv_x3f_1062_;
v_dec_x3f_1035_ = v___x_1074_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___y_1064_;
goto v___jp_1033_;
}
}
}
v___jp_971_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc_ref_n(v___y_974_, 2);
v___x_982_ = l_Array_append___redArg(v___y_974_, v___y_981_);
lean_dec_ref(v___y_981_);
lean_inc_n(v___y_980_, 4);
lean_inc_n(v___y_978_, 17);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___y_978_);
lean_ctor_set(v___x_983_, 1, v___y_980_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__9));
v___x_985_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__11));
v___x_986_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__7));
v___x_987_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__5));
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___y_978_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___y_978_, v___x_986_, v___x_988_, v___y_972_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v___y_978_);
lean_ctor_set(v___x_990_, 1, v___y_980_);
lean_ctor_set(v___x_990_, 2, v___y_974_);
lean_inc_ref_n(v___x_990_, 5);
v___x_991_ = l_Lean_Syntax_node2(v___y_978_, v___x_985_, v___x_989_, v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__3));
v___x_993_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__4));
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v___y_978_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__1));
v___x_996_ = l_Lean_Syntax_node2(v___y_978_, v___x_995_, v___x_990_, v___y_979_);
v___x_997_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__5));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_978_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__8));
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoWhile___closed__9));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_978_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node1(v___y_978_, v___x_999_, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node2(v___y_978_, v___x_985_, v___x_1002_, v___x_990_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_978_, v___y_980_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node1(v___y_978_, v___x_984_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node6(v___y_978_, v___x_992_, v___x_994_, v___x_996_, v___x_998_, v___x_1005_, v___x_990_, v___x_990_);
v___x_1007_ = l_Lean_Syntax_node2(v___y_978_, v___x_985_, v___x_1006_, v___x_990_);
v___x_1008_ = l_Lean_Syntax_node2(v___y_978_, v___y_980_, v___x_991_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node1(v___y_978_, v___x_984_, v___x_1008_);
lean_inc(v___y_976_);
v___x_1010_ = l_Lean_Syntax_node4(v___y_978_, v___y_976_, v___y_973_, v___y_977_, v___x_983_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___y_975_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoRepeatUntil___boxed(lean_object* v_x_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_Do_expandDoRepeatUntil(v_x_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1089_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1(){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1097_ = l_Lean_Elab_macroAttribute;
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Do_expandDoRepeatUntil___closed__3));
v___x_1099_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___closed__1));
v___x_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoRepeatUntil___boxed), 3, 0);
v___x_1101_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1097_, v___x_1098_, v___x_1099_, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1102_;
v_res_1102_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
stack->m_obj
 = v_res_1102_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1___boxed(lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_expandDoRepeatUntil___regBuiltin_Lean_Elab_Do_expandDoRepeatUntil__1();
return v_res_1104_;
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
