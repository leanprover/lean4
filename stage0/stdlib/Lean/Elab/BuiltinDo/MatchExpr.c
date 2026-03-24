// Lean compiler output
// Module: Lean.Elab.BuiltinDo.MatchExpr
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar import Lean.Elab.BuiltinDo.Basic import Init.Omega
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_withDuplicableCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "match_expr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BuiltinDo"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 37, 9, 26, 98, 187, 35)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 189, 152, 89, 18, 39, 213, 32)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 157, 115, 249, 219, 101, 200, 85)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 16, 195, 27, 23, 157, 197, 205)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(53, 176, 240, 177, 7, 187, 206, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 93, 19, 198, 66, 118, 152, 13)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandDoLetExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(134, 253, 173, 213, 231, 15, 207, 23)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expandDoLetMetaExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 90, 112, 164, 175, 179, 176, 45)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "match_expr else alternative"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "match_expr alternative "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__x"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 215, 60, 46, 39, 217, 189, 106)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "instantiateMVarsIfMVarApp"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(180, 221, 231, 68, 33, 162, 30, 45)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(97, 89, 84, 0, 241, 26, 4, 203)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabDoMatchExpr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 115, 111, 111, 24, 156, 126, 219)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(lean_object* v_stx_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4));
lean_inc(v_stx_59_);
v___x_63_ = l_Lean_Syntax_isOfKind(v_stx_59_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec(v_stx_59_);
v___x_64_ = l_Lean_Macro_throwUnsupported___redArg(v_a_61_);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = l_Lean_Syntax_getArg(v_stx_59_, v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6));
lean_inc(v___x_66_);
v___x_68_ = l_Lean_Syntax_isOfKind(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec(v___x_66_);
lean_dec(v_stx_59_);
v___x_69_ = l_Lean_Macro_throwUnsupported___redArg(v_a_61_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_70_ = lean_unsigned_to_nat(6u);
v___x_71_ = l_Lean_Syntax_getArg(v_stx_59_, v___x_70_);
lean_inc(v___x_71_);
v___x_72_ = l_Lean_Syntax_matchesNull(v___x_71_, v___x_65_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec(v___x_71_);
lean_dec(v___x_66_);
lean_dec(v_stx_59_);
v___x_73_ = l_Lean_Macro_throwUnsupported___redArg(v_a_61_);
return v___x_73_;
}
else
{
lean_object* v_ref_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_ref_74_ = lean_ctor_get(v_a_60_, 5);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_unsigned_to_nat(3u);
v___x_77_ = l_Lean_Syntax_getArg(v_stx_59_, v___x_76_);
v___x_78_ = lean_unsigned_to_nat(5u);
v___x_79_ = l_Lean_Syntax_getArg(v_stx_59_, v___x_78_);
lean_dec(v_stx_59_);
v___x_80_ = l_Lean_Syntax_getArg(v___x_71_, v___x_75_);
lean_dec(v___x_71_);
v___x_81_ = 0;
v___x_82_ = l_Lean_SourceInfo_fromRef(v_ref_74_, v___x_81_);
v___x_83_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
v___x_84_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(v___x_82_);
v___x_85_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
v___x_87_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12));
lean_inc(v___x_82_);
v___x_88_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13));
lean_inc(v___x_82_);
v___x_90_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_82_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14));
lean_inc(v___x_82_);
v___x_92_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_82_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15));
lean_inc(v___x_82_);
v___x_94_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_82_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16));
lean_inc(v___x_82_);
v___x_96_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_82_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_inc(v___x_82_);
v___x_97_ = l_Lean_Syntax_node5(v___x_82_, v___x_86_, v___x_88_, v___x_90_, v___x_92_, v___x_94_, v___x_96_);
v___x_98_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(v___x_82_);
v___x_99_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_82_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19));
v___x_101_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
v___x_102_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(v___x_82_);
v___x_103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_82_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(v___x_82_);
v___x_105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_82_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_inc_ref(v___x_105_);
lean_inc_ref(v___x_103_);
lean_inc(v___x_82_);
v___x_106_ = l_Lean_Syntax_node4(v___x_82_, v___x_101_, v___x_103_, v___x_66_, v___x_105_, v___x_80_);
lean_inc(v___x_82_);
v___x_107_ = l_Lean_Syntax_node1(v___x_82_, v___x_86_, v___x_106_);
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25));
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27));
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28));
lean_inc(v___x_82_);
v___x_111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_82_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
lean_inc(v___x_82_);
v___x_112_ = l_Lean_Syntax_node1(v___x_82_, v___x_109_, v___x_111_);
lean_inc(v___x_82_);
v___x_113_ = l_Lean_Syntax_node4(v___x_82_, v___x_108_, v___x_103_, v___x_112_, v___x_105_, v___x_79_);
lean_inc(v___x_82_);
v___x_114_ = l_Lean_Syntax_node2(v___x_82_, v___x_100_, v___x_107_, v___x_113_);
v___x_115_ = l_Lean_Syntax_node5(v___x_82_, v___x_83_, v___x_85_, v___x_97_, v___x_77_, v___x_99_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_61_);
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed(lean_object* v_stx_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(v_stx_117_, v_a_118_, v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1(){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = l_Lean_Elab_macroAttribute;
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4));
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15));
v___x_161_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed), 3, 0);
v___x_162_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_158_, v___x_159_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
return v_res_164_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Array_mkArray0(lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(lean_object* v_stx_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1));
lean_inc(v_stx_172_);
v___x_176_ = l_Lean_Syntax_isOfKind(v_stx_172_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec(v_stx_172_);
v___x_177_ = l_Lean_Macro_throwUnsupported___redArg(v_a_174_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6));
lean_inc(v___x_179_);
v___x_181_ = l_Lean_Syntax_isOfKind(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v___x_179_);
lean_dec(v_stx_172_);
v___x_182_ = l_Lean_Macro_throwUnsupported___redArg(v_a_174_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(6u);
v___x_184_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_183_);
lean_inc(v___x_184_);
v___x_185_ = l_Lean_Syntax_matchesNull(v___x_184_, v___x_178_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec(v___x_184_);
lean_dec(v___x_179_);
lean_dec(v_stx_172_);
v___x_186_ = l_Lean_Macro_throwUnsupported___redArg(v_a_174_);
return v___x_186_;
}
else
{
lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_ref_187_ = lean_ctor_get(v_a_173_, 5);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_unsigned_to_nat(3u);
v___x_190_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_189_);
v___x_191_ = lean_unsigned_to_nat(5u);
v___x_192_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_191_);
lean_dec(v_stx_172_);
v___x_193_ = l_Lean_Syntax_getArg(v___x_184_, v___x_188_);
lean_dec(v___x_184_);
v___x_194_ = 0;
v___x_195_ = l_Lean_SourceInfo_fromRef(v_ref_187_, v___x_194_);
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(v___x_195_);
v___x_198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_195_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
v___x_200_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2);
lean_inc(v___x_195_);
v___x_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_195_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(v___x_195_);
v___x_203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_195_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19));
v___x_205_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(v___x_195_);
v___x_207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_195_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(v___x_195_);
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_195_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
lean_inc_ref(v___x_209_);
lean_inc_ref(v___x_207_);
lean_inc(v___x_195_);
v___x_210_ = l_Lean_Syntax_node4(v___x_195_, v___x_205_, v___x_207_, v___x_179_, v___x_209_, v___x_193_);
lean_inc(v___x_195_);
v___x_211_ = l_Lean_Syntax_node1(v___x_195_, v___x_199_, v___x_210_);
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25));
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27));
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28));
lean_inc(v___x_195_);
v___x_215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_195_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_inc(v___x_195_);
v___x_216_ = l_Lean_Syntax_node1(v___x_195_, v___x_213_, v___x_215_);
lean_inc(v___x_195_);
v___x_217_ = l_Lean_Syntax_node4(v___x_195_, v___x_212_, v___x_207_, v___x_216_, v___x_209_, v___x_192_);
lean_inc(v___x_195_);
v___x_218_ = l_Lean_Syntax_node2(v___x_195_, v___x_204_, v___x_211_, v___x_217_);
v___x_219_ = l_Lean_Syntax_node5(v___x_195_, v___x_196_, v___x_198_, v___x_201_, v___x_190_, v___x_203_, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_174_);
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed(lean_object* v_stx_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(v_stx_221_, v_a_222_, v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1(){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_230_ = l_Lean_Elab_macroAttribute;
v___x_231_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1));
v___x_232_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1));
v___x_233_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed), 3, 0);
v___x_234_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_230_, v___x_231_, v___x_232_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___boxed(lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
return v_res_236_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___boxed(lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(lean_object* v_00_u03b1_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(v_00_u03b1_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(uint8_t v___x_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v_discr_270_, uint8_t v___x_271_, lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v_alts_274_, lean_object* v_altsArr_275_, lean_object* v_rhs_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___y_286_; lean_object* v___y_308_; lean_object* v_info_309_; lean_object* v_kind_310_; lean_object* v_args_311_; 
if (lean_obj_tag(v_alts_274_) == 1)
{
lean_object* v_info_320_; lean_object* v_kind_321_; lean_object* v_args_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_info_320_ = lean_ctor_get(v_alts_274_, 0);
lean_inc(v_info_320_);
v_kind_321_ = lean_ctor_get(v_alts_274_, 1);
lean_inc(v_kind_321_);
v_args_322_ = lean_ctor_get(v_alts_274_, 2);
lean_inc_ref(v_args_322_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_args_322_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v_altsArr_275_);
v___y_308_ = v_alts_274_;
v_info_309_ = v_info_320_;
v_kind_310_ = v_kind_321_;
v_args_311_ = v_args_322_;
goto v___jp_307_;
}
else
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_337_; 
v_isSharedCheck_337_ = !lean_is_exclusive(v_alts_274_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_338_ = lean_ctor_get(v_alts_274_, 2);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_alts_274_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_alts_274_, 0);
lean_dec(v_unused_340_);
v___x_327_ = v_alts_274_;
v_isShared_328_ = v_isSharedCheck_337_;
goto v_resetjp_326_;
}
else
{
lean_dec(v_alts_274_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_337_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_v_329_; lean_object* v___x_330_; lean_object* v_xs_x27_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v_v_329_ = lean_array_fget(v_args_322_, v___x_323_);
v___x_330_ = lean_box(0);
v_xs_x27_331_ = lean_array_fset(v_args_322_, v___x_323_, v___x_330_);
v___x_332_ = l_Lean_Syntax_setArgs(v_v_329_, v_altsArr_275_);
v___x_333_ = lean_array_fset(v_xs_x27_331_, v___x_323_, v___x_332_);
lean_inc_ref(v___x_333_);
lean_inc(v_kind_321_);
lean_inc(v_info_320_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 2, v___x_333_);
v___x_335_ = v___x_327_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_info_320_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_kind_321_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v___y_308_ = v___x_335_;
v_info_309_ = v_info_320_;
v_kind_310_ = v_kind_321_;
v_args_311_ = v___x_333_;
goto v___jp_307_;
}
}
}
}
else
{
lean_dec_ref(v_altsArr_275_);
if (lean_obj_tag(v_alts_274_) == 1)
{
lean_object* v_info_341_; lean_object* v_kind_342_; lean_object* v_args_343_; 
v_info_341_ = lean_ctor_get(v_alts_274_, 0);
lean_inc(v_info_341_);
v_kind_342_ = lean_ctor_get(v_alts_274_, 1);
lean_inc(v_kind_342_);
v_args_343_ = lean_ctor_get(v_alts_274_, 2);
lean_inc_ref(v_args_343_);
v___y_308_ = v_alts_274_;
v_info_309_ = v_info_341_;
v_kind_310_ = v_kind_342_;
v_args_311_ = v_args_343_;
goto v___jp_307_;
}
else
{
lean_dec(v_rhs_276_);
v___y_286_ = v_alts_274_;
goto v___jp_285_;
}
}
v___jp_285_:
{
lean_object* v_doBlockResultType_287_; lean_object* v___x_288_; 
v_doBlockResultType_287_ = lean_ctor_get(v___y_277_, 3);
lean_inc_ref(v_doBlockResultType_287_);
v___x_288_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_287_, v___y_277_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_306_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_306_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_306_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_306_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_ref_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v_ref_293_ = lean_ctor_get(v___y_282_, 5);
v___x_294_ = l_Lean_SourceInfo_fromRef(v_ref_293_, v___x_266_);
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0));
v___x_296_ = l_Lean_Name_mkStr4(v___x_267_, v___x_268_, v___x_269_, v___x_295_);
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9));
lean_inc(v___x_294_);
v___x_298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17));
lean_inc(v___x_294_);
v___x_300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_294_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_Syntax_node4(v___x_294_, v___x_296_, v___x_298_, v_discr_270_, v___x_300_, v___y_286_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 1);
v___x_303_ = v___x_291_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_289_);
v___x_303_ = v_reuseFailAlloc_305_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Elab_Term_elabTerm(v___x_301_, v___x_303_, v___x_271_, v___x_271_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_304_;
}
}
}
else
{
lean_dec(v___y_286_);
lean_dec(v_discr_270_);
lean_dec_ref(v___x_269_);
lean_dec_ref(v___x_268_);
lean_dec_ref(v___x_267_);
return v___x_288_;
}
}
v___jp_307_:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_array_get_size(v_args_311_);
v___x_313_ = lean_nat_dec_lt(v___x_272_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_args_311_);
lean_dec(v_kind_310_);
lean_dec(v_info_309_);
lean_dec(v_rhs_276_);
v___y_286_ = v___y_308_;
goto v___jp_285_;
}
else
{
lean_object* v_v_314_; lean_object* v___x_315_; lean_object* v_xs_x27_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v___y_308_);
v_v_314_ = lean_array_fget(v_args_311_, v___x_272_);
v___x_315_ = lean_box(0);
v_xs_x27_316_ = lean_array_fset(v_args_311_, v___x_272_, v___x_315_);
v___x_317_ = l_Lean_Syntax_setArg(v_v_314_, v___x_273_, v_rhs_276_);
v___x_318_ = lean_array_fset(v_xs_x27_316_, v___x_272_, v___x_317_);
v___x_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_319_, 0, v_info_309_);
lean_ctor_set(v___x_319_, 1, v_kind_310_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
v___y_286_ = v___x_319_;
goto v___jp_285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed(lean_object** _args){
lean_object* v___x_344_ = _args[0];
lean_object* v___x_345_ = _args[1];
lean_object* v___x_346_ = _args[2];
lean_object* v___x_347_ = _args[3];
lean_object* v_discr_348_ = _args[4];
lean_object* v___x_349_ = _args[5];
lean_object* v___x_350_ = _args[6];
lean_object* v___x_351_ = _args[7];
lean_object* v_alts_352_ = _args[8];
lean_object* v_altsArr_353_ = _args[9];
lean_object* v_rhs_354_ = _args[10];
lean_object* v___y_355_ = _args[11];
lean_object* v___y_356_ = _args[12];
lean_object* v___y_357_ = _args[13];
lean_object* v___y_358_ = _args[14];
lean_object* v___y_359_ = _args[15];
lean_object* v___y_360_ = _args[16];
lean_object* v___y_361_ = _args[17];
lean_object* v___y_362_ = _args[18];
_start:
{
uint8_t v___x_7008__boxed_363_; uint8_t v___x_7012__boxed_364_; lean_object* v_res_365_; 
v___x_7008__boxed_363_ = lean_unbox(v___x_344_);
v___x_7012__boxed_364_ = lean_unbox(v___x_349_);
v_res_365_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(v___x_7008__boxed_363_, v___x_345_, v___x_346_, v___x_347_, v_discr_348_, v___x_7012__boxed_364_, v___x_350_, v___x_351_, v_alts_352_, v_altsArr_353_, v_rhs_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___x_351_);
lean_dec(v___x_350_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed(lean_object** _args){
lean_object* v___x_369_ = _args[0];
lean_object* v_pattern_370_ = _args[1];
lean_object* v_i_371_ = _args[2];
lean_object* v___x_372_ = _args[3];
lean_object* v_altsArr_373_ = _args[4];
lean_object* v_discr_374_ = _args[5];
lean_object* v_alts_375_ = _args[6];
lean_object* v_dec_376_ = _args[7];
lean_object* v_rhs_377_ = _args[8];
lean_object* v___y_378_ = _args[9];
lean_object* v___y_379_ = _args[10];
lean_object* v___y_380_ = _args[11];
lean_object* v___y_381_ = _args[12];
lean_object* v___y_382_ = _args[13];
lean_object* v___y_383_ = _args[14];
lean_object* v___y_384_ = _args[15];
lean_object* v___y_385_ = _args[16];
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(v___x_369_, v_pattern_370_, v_i_371_, v___x_372_, v_altsArr_373_, v_discr_374_, v_alts_375_, v_dec_376_, v_rhs_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___x_372_);
lean_dec(v_i_371_);
return v_res_386_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(lean_object* v_discr_390_, lean_object* v_alts_391_, lean_object* v_dec_392_, lean_object* v_i_393_, lean_object* v_altsArr_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_array_get_size(v_altsArr_394_);
v___x_404_ = lean_nat_dec_lt(v_i_393_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_elseSeq_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_i_393_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = l_Lean_Syntax_getArg(v_alts_391_, v___x_405_);
v___x_407_ = lean_unsigned_to_nat(3u);
v_elseSeq_408_ = l_Lean_Syntax_getArg(v___x_406_, v___x_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1);
v___x_410_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0));
v___x_411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2));
v___x_413_ = 1;
v___x_414_ = lean_box(v___x_404_);
v___x_415_ = lean_box(v___x_413_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed), 19, 10);
lean_closure_set(v___f_416_, 0, v___x_414_);
lean_closure_set(v___f_416_, 1, v___x_410_);
lean_closure_set(v___f_416_, 2, v___x_411_);
lean_closure_set(v___f_416_, 3, v___x_412_);
lean_closure_set(v___f_416_, 4, v_discr_390_);
lean_closure_set(v___f_416_, 5, v___x_415_);
lean_closure_set(v___f_416_, 6, v___x_405_);
lean_closure_set(v___f_416_, 7, v___x_407_);
lean_closure_set(v___f_416_, 8, v_alts_391_);
lean_closure_set(v___f_416_, 9, v_altsArr_394_);
v___x_417_ = lean_box(v___x_413_);
lean_inc(v_elseSeq_408_);
v___x_418_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_418_, 0, v_elseSeq_408_);
lean_closure_set(v___x_418_, 1, v_dec_392_);
lean_closure_set(v___x_418_, 2, v___x_417_);
v___x_419_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_409_, v___x_418_, v___f_416_, v_elseSeq_408_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_elseSeq_408_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_array_fget(v_altsArr_394_, v_i_393_);
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21));
lean_inc(v___x_420_);
v___x_422_ = l_Lean_Syntax_isOfKind(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v___x_420_);
lean_dec_ref(v_altsArr_394_);
lean_dec(v_i_393_);
lean_dec_ref(v_dec_392_);
lean_dec(v_alts_391_);
lean_dec(v_discr_390_);
v___x_423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v_pattern_425_; lean_object* v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v_pattern_425_ = l_Lean_Syntax_getArg(v___x_420_, v___x_424_);
lean_inc(v_pattern_425_);
v___x_426_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_pattern_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
v___x_428_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v_a_427_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v___x_428_);
lean_inc_ref(v_dec_392_);
lean_inc(v_pattern_425_);
v___f_429_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed), 17, 8);
lean_closure_set(v___f_429_, 0, v___x_421_);
lean_closure_set(v___f_429_, 1, v_pattern_425_);
lean_closure_set(v___f_429_, 2, v_i_393_);
lean_closure_set(v___f_429_, 3, v___x_424_);
lean_closure_set(v___f_429_, 4, v_altsArr_394_);
lean_closure_set(v___f_429_, 5, v_discr_390_);
lean_closure_set(v___f_429_, 6, v_alts_391_);
lean_closure_set(v___f_429_, 7, v_dec_392_);
v___x_430_ = lean_unsigned_to_nat(3u);
v___x_431_ = l_Lean_Syntax_getArg(v___x_420_, v___x_430_);
lean_dec(v___x_420_);
v___x_432_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3);
v___x_433_ = l_Lean_MessageData_ofSyntax(v_pattern_425_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_box(v___x_422_);
lean_inc(v___x_431_);
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_436_, 0, v___x_431_);
lean_closure_set(v___x_436_, 1, v_dec_392_);
lean_closure_set(v___x_436_, 2, v___x_435_);
v___x_437_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_434_, v___x_436_, v___f_429_, v___x_431_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v___x_431_);
return v___x_437_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_pattern_425_);
lean_dec(v___x_420_);
lean_dec_ref(v_altsArr_394_);
lean_dec(v_i_393_);
lean_dec_ref(v_dec_392_);
lean_dec(v_alts_391_);
lean_dec(v_discr_390_);
v_a_438_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_428_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_428_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_pattern_425_);
lean_dec(v___x_420_);
lean_dec_ref(v_altsArr_394_);
lean_dec(v_i_393_);
lean_dec_ref(v_dec_392_);
lean_dec(v_alts_391_);
lean_dec(v_discr_390_);
v_a_446_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_426_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_426_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(lean_object* v___x_454_, lean_object* v_pattern_455_, lean_object* v_i_456_, lean_object* v___x_457_, lean_object* v_altsArr_458_, lean_object* v_discr_459_, lean_object* v_alts_460_, lean_object* v_dec_461_, lean_object* v_rhs_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_ref_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_ref_471_ = lean_ctor_get(v___y_468_, 5);
v___x_472_ = 0;
v___x_473_ = l_Lean_SourceInfo_fromRef(v_ref_471_, v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22));
lean_inc(v___x_473_);
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23));
lean_inc(v___x_473_);
v___x_477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_473_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_Syntax_node4(v___x_473_, v___x_454_, v___x_475_, v_pattern_455_, v___x_477_, v_rhs_462_);
v___x_479_ = lean_nat_add(v_i_456_, v___x_457_);
v___x_480_ = lean_array_fset(v_altsArr_458_, v_i_456_, v___x_478_);
v___x_481_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_459_, v_alts_460_, v_dec_461_, v___x_479_, v___x_480_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___boxed(lean_object* v_discr_482_, lean_object* v_alts_483_, lean_object* v_dec_484_, lean_object* v_i_485_, lean_object* v_altsArr_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_482_, v_alts_483_, v_dec_484_, v_i_485_, v_altsArr_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_499_ == 0)
{
return v_bs_498_;
}
else
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v_v_500_ = lean_array_uget(v_bs_498_, v_i_497_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_501_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_497_, v___x_503_);
v___x_505_ = lean_array_uset(v_bs_x27_502_, v_i_497_, v_v_500_);
v_i_497_ = v___x_504_;
v_bs_498_ = v___x_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0___boxed(lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_){
_start:
{
size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_sz_boxed_510_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(v_sz_boxed_510_, v_i_boxed_511_, v_bs_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(lean_object* v_alts_513_, lean_object* v_discr_514_, lean_object* v_dec_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_Syntax_getArg(v_alts_513_, v___x_524_);
v___x_526_ = l_Lean_Syntax_getArgs(v___x_525_);
lean_dec(v___x_525_);
v_sz_527_ = lean_array_size(v___x_526_);
v___x_528_ = ((size_t)0ULL);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(v_sz_527_, v___x_528_, v___x_526_);
v___x_530_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_514_, v_alts_513_, v_dec_515_, v___x_524_, v___x_529_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed(lean_object* v_alts_531_, lean_object* v_discr_532_, lean_object* v_dec_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(v_alts_531_, v_discr_532_, v_dec_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(lean_object* v_info_543_, lean_object* v_discr_544_, lean_object* v_alts_545_, lean_object* v_dec_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___f_555_; lean_object* v___x_556_; 
v___f_555_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed), 11, 2);
lean_closure_set(v___f_555_, 0, v_alts_545_);
lean_closure_set(v___f_555_, 1, v_discr_544_);
lean_inc_ref(v_a_547_);
v___x_556_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(v_dec_546_, v_info_543_, v___f_555_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed(lean_object* v_info_557_, lean_object* v_discr_558_, lean_object* v_alts_559_, lean_object* v_dec_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_info_557_, v_discr_558_, v_alts_559_, v_dec_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec_ref(v_a_561_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6));
v___x_587_ = l_String_toRawSubstring_x27(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(lean_object* v_stx_601_, lean_object* v_dec_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v_metaFalseTk_x3f_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
lean_inc(v_stx_601_);
v___x_612_ = l_Lean_Syntax_isOfKind(v_stx_601_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v_dec_602_);
lean_dec(v_stx_601_);
v___x_670_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = l_Lean_Syntax_getArg(v_stx_601_, v___x_671_);
v___x_673_ = l_Lean_Syntax_isNone(v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_672_);
v___x_675_ = l_Lean_Syntax_matchesNull(v___x_672_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v___x_672_);
lean_dec_ref(v_dec_602_);
lean_dec(v_stx_601_);
v___x_676_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v_metaFalseTk_x3f_678_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(4u);
v_metaFalseTk_x3f_678_ = l_Lean_Syntax_getArg(v___x_672_, v___x_677_);
lean_dec(v___x_672_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_metaFalseTk_x3f_678_);
lean_inc_ref(v_a_608_);
v_metaFalseTk_x3f_614_ = v___x_679_;
v___y_615_ = v_a_603_;
v___y_616_ = v_a_604_;
v___y_617_ = v_a_605_;
v___y_618_ = v_a_606_;
v___y_619_ = v_a_607_;
v___y_620_ = v_a_608_;
v___y_621_ = v_a_609_;
goto v___jp_613_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_672_);
v___x_680_ = lean_box(0);
lean_inc_ref(v_a_608_);
v_metaFalseTk_x3f_614_ = v___x_680_;
v___y_615_ = v_a_603_;
v___y_616_ = v_a_604_;
v___y_617_ = v_a_605_;
v___y_618_ = v_a_606_;
v___y_619_ = v_a_607_;
v___y_620_ = v_a_608_;
v___y_621_ = v_a_609_;
goto v___jp_613_;
}
}
v___jp_613_:
{
lean_object* v___x_622_; 
lean_inc(v_stx_601_);
v___x_622_ = l_Lean_Elab_Do_inferControlInfoElem(v_stx_601_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v_discr_625_; lean_object* v___x_626_; lean_object* v_alts_627_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_622_);
v___x_624_ = lean_unsigned_to_nat(2u);
v_discr_625_ = l_Lean_Syntax_getArg(v_stx_601_, v___x_624_);
v___x_626_ = lean_unsigned_to_nat(4u);
v_alts_627_ = l_Lean_Syntax_getArg(v_stx_601_, v___x_626_);
lean_dec(v_stx_601_);
if (lean_obj_tag(v_metaFalseTk_x3f_614_) == 0)
{
if (v___x_612_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_a_623_, v_discr_625_, v_alts_627_, v_dec_602_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec_ref(v___y_620_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1));
v___x_630_ = l_Lean_Core_mkFreshUserName(v___x_629_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_ref_632_; lean_object* v_quotContext_633_; lean_object* v_currMacroScope_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v_ref_632_ = lean_ctor_get(v___y_620_, 5);
v_quotContext_633_ = lean_ctor_get(v___y_620_, 10);
v_currMacroScope_634_ = lean_ctor_get(v___y_620_, 11);
v___x_635_ = 0;
v___x_636_ = l_Lean_mkIdentFrom(v_discr_625_, v_a_631_, v___x_635_);
v___x_637_ = l_Lean_SourceInfo_fromRef(v_ref_632_, v___x_635_);
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3));
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5));
v___x_640_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7, &l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7);
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8));
lean_inc(v_currMacroScope_634_);
lean_inc(v_quotContext_633_);
v___x_642_ = l_Lean_addMacroScope(v_quotContext_633_, v___x_641_, v_currMacroScope_634_);
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12));
lean_inc(v___x_637_);
v___x_644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_644_, 0, v___x_637_);
lean_ctor_set(v___x_644_, 1, v___x_640_);
lean_ctor_set(v___x_644_, 2, v___x_642_);
lean_ctor_set(v___x_644_, 3, v___x_643_);
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11));
lean_inc(v___x_637_);
v___x_646_ = l_Lean_Syntax_node1(v___x_637_, v___x_645_, v_discr_625_);
lean_inc(v___x_637_);
v___x_647_ = l_Lean_Syntax_node2(v___x_637_, v___x_639_, v___x_644_, v___x_646_);
v___x_648_ = l_Lean_Syntax_node1(v___x_637_, v___x_638_, v___x_647_);
v___x_649_ = lean_box(0);
lean_inc(v___x_636_);
v___x_650_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed), 12, 4);
lean_closure_set(v___x_650_, 0, v_a_623_);
lean_closure_set(v___x_650_, 1, v___x_636_);
lean_closure_set(v___x_650_, 2, v_alts_627_);
lean_closure_set(v___x_650_, 3, v_dec_602_);
v___x_651_ = 0;
lean_inc_ref(v___y_618_);
v___x_652_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_636_, v___x_649_, v___x_648_, v___x_650_, v___x_651_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec_ref(v___y_620_);
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_alts_627_);
lean_dec(v_discr_625_);
lean_dec(v_a_623_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_dec_602_);
v_a_653_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_630_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_630_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v___x_661_; 
lean_dec_ref(v_metaFalseTk_x3f_614_);
v___x_661_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_a_623_, v_discr_625_, v_alts_627_, v_dec_602_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec_ref(v___y_620_);
return v___x_661_;
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v___y_620_);
lean_dec(v_metaFalseTk_x3f_614_);
lean_dec_ref(v_dec_602_);
lean_dec(v_stx_601_);
v_a_662_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_622_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_622_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed(lean_object* v_stx_681_, lean_object* v_dec_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(v_stx_681_, v_dec_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_697_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_698_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8));
v___x_699_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1));
v___x_700_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed), 10, 0);
v___x_701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_697_, v___x_698_, v___x_699_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___boxed(lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
return v_res_703_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_MatchExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
}
#ifdef __cplusplus
}
#endif
