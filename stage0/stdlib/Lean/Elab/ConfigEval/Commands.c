// Lean compiler output
// Module: Lean.Elab.ConfigEval.Commands
// Imports: public import Lean.Elab.ConfigEval.DeriveEvalTerm public meta import Lean.Elab.ConfigEval.DeriveEvalTerm public import Lean.Elab.ConfigEval.DeriveEvalExpr public meta import Lean.Elab.ConfigEval.DeriveEvalExpr public import Lean.Elab.ConfigEval.DeriveEvalConfigItem public meta import Lean.Elab.ConfigEval.DeriveEvalConfigItem public import Lean.Elab.Tactic.ElabTerm import Lean.Linter.MissingDocs
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
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ensureEvalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ensureEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigEval"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "command__Ensure_eval_term_instance_"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 35, 25, 249, 138, 104, 126, 162)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "visibility"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__9_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 205, 25, 140, 55, 50, 241, 254)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__10_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__10_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__11_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__13_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__13_value),LEAN_SCALAR_PTR_LITERAL(144, 113, 220, 36, 163, 13, 57, 223)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__14_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__15_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__12_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__15_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "ensure_eval_term_instance "};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__17 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__17_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__17_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__18 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__18_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__19 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__19_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__20 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__20_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__20_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__21 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__21_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__19_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__23 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__23_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__23_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__24 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__24_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance__ = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__24_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "command__Ensure_eval_expr_instance_"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 4, 45, 227, 207, 151, 31, 106)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "ensure_eval_expr_instance "};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__5_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance__ = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__expr__instance____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__expr__instance____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "command__Ensure_eval_term_expr_instances_"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 62, 158, 116, 163, 180, 194, 228)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ensure_eval_term_expr_instances "};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__5_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances__ = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ensure_eval_term_instance"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ensure_eval_expr_instance"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4;
static const lean_array_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "command__Derive_eval_expr_instance_using_meta_eval_"};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 183, 63, 252, 111, 88, 79, 15)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "derive_eval_expr_instance_using_meta_eval "};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__16_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__22_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__5_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval__ = (const lean_object*)&l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Derive__eval__expr__instance__using__meta__eval____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Derive__eval__expr__instance__using__meta__eval____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "configEntryOmit"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 140, 111, 202, 251, 168, 170, 75)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omit "};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__7;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__10;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryOmit___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryOmit___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "configEntryHandlerKeyPrefix"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 45, 37, 228, 14, 221, 193, 71)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "configEntryHandlerKeyWildcard"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 192, 13, 21, 20, 44, 232, 93)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "configEntryHandlerKey"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 190, 73, 235, 170, 184, 39, 210)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "configEntryHandler"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 145, 34, 65, 77, 53, 67, 42)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "option "};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__7;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__10;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__11;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__12;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "configEntry"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 149, 160, 204, 146, 200, 218, 133)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "configEntries"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 127, 108, 166, 156, 181, 170, 30)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_configEntries___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__7_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__9;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__10_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__11;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__12;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__13;
static const lean_string_object l_Lean_Elab_ConfigEval_configEntries___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__15;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__16;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__17;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__18;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__19;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__20;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__21;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__22;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__23;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "defEvalConfigItemCmd"};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 50, 201, 157, 117, 233, 235, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__12_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__15_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value;
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "def_eval_config_item "};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value;
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bracketedBinder"};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(126, 188, 9, 177, 18, 110, 216, 30)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value;
static const lean_string_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__8_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__26 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__26_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__26_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__27 = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__27_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItemCmd = (const lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__27_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__4_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__4_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__6_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__6_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__7_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__7_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__8_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__8_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntry_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntry_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntry___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_configEntries___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__defEvalConfigItemCmd__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__defEvalConfigItemCmd__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config elab"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "strictImplicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(125, 223, 215, 186, 222, 17, 242, 189)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unsupported binder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binderDefault"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "EvalConfigItem.defaultOnErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "defaultOnErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cfgType\?"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value),LEAN_SCALAR_PTR_LITERAL(58, 117, 29, 104, 229, 209, 250, 101)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkConst"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value),LEAN_SCALAR_PTR_LITERAL(37, 117, 8, 90, 26, 147, 93, 249)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value),LEAN_SCALAR_PTR_LITERAL(28, 38, 193, 74, 165, 73, 8, 119)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "logExceptions"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value),LEAN_SCALAR_PTR_LITERAL(118, 86, 185, 206, 146, 131, 198, 232)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 38, 228, 229, 249, 19, 211)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "EvalConfigItem.setConfig'"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "EvalConfigItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setConfig'"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value),LEAN_SCALAR_PTR_LITERAL(22, 247, 23, 93, 100, 235, 111, 189)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value),LEAN_SCALAR_PTR_LITERAL(64, 183, 169, 121, 35, 91, 151, 47)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_value),LEAN_SCALAR_PTR_LITERAL(16, 84, 54, 65, 212, 237, 250, 172)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_3),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value),LEAN_SCALAR_PTR_LITERAL(190, 187, 222, 86, 238, 13, 118, 125)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value),LEAN_SCALAR_PTR_LITERAL(12, 151, 53, 232, 164, 85, 213, 132)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "onErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value),LEAN_SCALAR_PTR_LITERAL(228, 46, 52, 217, 218, 46, 201, 51)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalConfigItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_value),LEAN_SCALAR_PTR_LITERAL(180, 209, 241, 176, 164, 63, 27, 216)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "def_eval_config_item"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__112 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__112_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabDeclareCoreConfigElab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 169, 247, 122, 199, 9, 42, 189)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declare_core_config_elab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "CoreM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 126, 120, 188, 150, 235, 117, 203)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 114, 191, 177, 45, 189, 121, 141)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabDeclareTermConfigElab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 129, 201, 91, 36, 24, 34, 115)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declare_term_config_elab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__9_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_&&_"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 195, 203, 117, 177, 125, 57, 22)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "read"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(190, 16, 165, 175, 2, 23, 214, 231)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__15_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadReader"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(11, 173, 117, 41, 17, 79, 142, 168)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(46, 74, 177, 199, 30, 224, 37, 71)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__18_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__19_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "errToSorry"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__20 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__20_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 138, 245, 152, 171, 48, 109)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__22 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "TermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3;
static const lean_closure_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___boxed, .m_arity = 8, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value)} };
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "elabDeclareTacticConfig"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 103, 219, 85, 28, 93, 217, 46)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "declare_config_elab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__7_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__8_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__9_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 177, 38, 2, 101, 67, 237, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TacticM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 63, 151, 54, 27, 84, 190, 214)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3;
static const lean_closure_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___boxed, .m_arity = 8, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value)} };
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "elabDeclareCommandConfig"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 75, 209, 24, 31, 135, 140, 54)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "declare_command_config_elab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__6_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__7_value),((lean_object*)&l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__8_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__9_value;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Command.liftTermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "liftTermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommandElabM"};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 183, 159, 6, 104, 246, 8, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___closed__0);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg___boxed(lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0(lean_object* v_00_u03b1_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___boxed(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0(v_00_u03b1_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___redArg(lean_object* v_a_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___redArg___boxed(lean_object* v_a_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___redArg(v_a_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1(lean_object* v_00_u03b1_91_, lean_object* v_a_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___boxed(lean_object* v_00_u03b1_101_, lean_object* v_a_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1(v_00_u03b1_101_, v_a_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1(lean_object* v_x_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4));
lean_inc(v_x_111_);
v___x_116_ = l_Lean_Syntax_isOfKind(v_x_111_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec(v_x_111_);
v___x_117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_kind_121_; lean_object* v___x_122_; lean_object* v_tk_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___y_127_; lean_object* v___x_142_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_111_, v___x_118_);
v___x_120_ = lean_unsigned_to_nat(1u);
v_kind_121_ = l_Lean_Syntax_getArg(v_x_111_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v_tk_123_ = l_Lean_Syntax_getArg(v_x_111_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_111_, v___x_124_);
lean_dec(v_x_111_);
v___x_142_ = l_Lean_Syntax_getOptional_x3f(v___x_119_);
lean_dec(v___x_119_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_box(0);
v___y_127_ = v___x_143_;
goto v___jp_126_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_val_144_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_val_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v___y_127_ = v___x_149_;
goto v___jp_126_;
}
}
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_box(0);
lean_inc(v___x_125_);
v___x_129_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_129_, 0, v___x_125_);
lean_closure_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___boxed), 9, 2);
lean_closure_set(v___x_130_, 0, lean_box(0));
lean_closure_set(v___x_130_, 1, v___x_129_);
v___x_131_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_130_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = l_Lean_Elab_ConfigEval_ensureEvalTerm(v___y_127_, v_kind_121_, v_tk_123_, v___x_125_, v_a_132_, v_a_112_, v_a_113_);
return v___x_133_;
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v___y_127_);
lean_dec(v___x_125_);
lean_dec(v_tk_123_);
lean_dec(v_kind_121_);
v_a_134_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_131_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_131_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1___boxed(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1(v_x_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__expr__instance____1(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1));
lean_inc(v_x_179_);
v___x_184_ = l_Lean_Syntax_isOfKind(v_x_179_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_dec(v_x_179_);
v___x_185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_kind_189_; lean_object* v___x_190_; lean_object* v_tk_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___y_195_; lean_object* v___x_210_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_179_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(1u);
v_kind_189_ = l_Lean_Syntax_getArg(v_x_179_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(2u);
v_tk_191_ = l_Lean_Syntax_getArg(v_x_179_, v___x_190_);
v___x_192_ = lean_unsigned_to_nat(3u);
v___x_193_ = l_Lean_Syntax_getArg(v_x_179_, v___x_192_);
lean_dec(v_x_179_);
v___x_210_ = l_Lean_Syntax_getOptional_x3f(v___x_187_);
lean_dec(v___x_187_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
v___y_195_ = v___x_211_;
goto v___jp_194_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_210_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_val_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
v___y_195_ = v___x_217_;
goto v___jp_194_;
}
}
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_196_ = lean_box(0);
lean_inc(v___x_193_);
v___x_197_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_197_, 0, v___x_193_);
lean_closure_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___boxed), 9, 2);
lean_closure_set(v___x_198_, 0, lean_box(0));
lean_closure_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_198_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_201_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(v___y_195_, v_kind_189_, v_tk_191_, v___x_193_, v_a_200_, v_a_180_, v_a_181_);
return v___x_201_;
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v___y_195_);
lean_dec(v___x_193_);
lean_dec(v_tk_191_);
lean_dec(v_kind_189_);
v_a_202_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_199_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_199_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__expr__instance____1___boxed(lean_object* v_x_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__expr__instance____1(v_x_220_, v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_224_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Array_mkArray0(lean_box(0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__expr__instances___00__closed__1));
lean_inc(v_x_255_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_255_);
v___x_260_ = lean_box(1);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_tk_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_289_; lean_object* v___x_299_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_255_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Lean_Syntax_getArg(v_x_255_, v___x_264_);
v___x_266_ = lean_unsigned_to_nat(2u);
v_tk_267_ = l_Lean_Syntax_getArg(v_x_255_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(3u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_255_, v___x_268_);
lean_dec(v_x_255_);
v___x_299_ = l_Lean_Syntax_getOptional_x3f(v___x_263_);
lean_dec(v___x_263_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
v___y_289_ = v___x_300_;
goto v___jp_288_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_val_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
v___y_289_ = v___x_306_;
goto v___jp_288_;
}
}
}
v___jp_270_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref(v___y_272_);
v___x_276_ = l_Array_append___redArg(v___y_272_, v___y_275_);
lean_dec_ref(v___y_275_);
lean_inc_n(v___y_274_, 2);
lean_inc_n(v___y_271_, 3);
v___x_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_277_, 0, v___y_271_);
lean_ctor_set(v___x_277_, 1, v___y_274_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
v___x_278_ = l_Lean_SourceInfo_fromRef(v_tk_267_, v___x_259_);
lean_dec(v_tk_267_);
v___x_279_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__0));
lean_inc(v___x_278_);
v___x_280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_inc(v___x_269_);
lean_inc(v___x_265_);
lean_inc_ref(v___x_277_);
lean_inc(v___y_273_);
v___x_281_ = l_Lean_Syntax_node4(v___y_271_, v___y_273_, v___x_277_, v___x_265_, v___x_280_, v___x_269_);
v___x_282_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__expr__instance___00__closed__1));
v___x_283_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__1));
v___x_284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_278_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_Syntax_node4(v___y_271_, v___x_282_, v___x_277_, v___x_265_, v___x_284_, v___x_269_);
v___x_286_ = l_Lean_Syntax_node2(v___y_271_, v___y_274_, v___x_281_, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_257_);
return v___x_287_;
}
v___jp_288_:
{
lean_object* v_ref_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_ref_290_ = lean_ctor_get(v_a_256_, 5);
v___x_291_ = 0;
v___x_292_ = l_Lean_SourceInfo_fromRef(v_ref_290_, v___x_291_);
v___x_293_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3));
v___x_294_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__4));
v___x_295_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4);
if (lean_obj_tag(v___y_289_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_297_; 
v_val_296_ = lean_ctor_get(v___y_289_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v___y_289_);
v___x_297_ = l_Array_mkArray1___redArg(v_val_296_);
v___y_271_ = v___x_292_;
v___y_272_ = v___x_295_;
v___y_273_ = v___x_294_;
v___y_274_ = v___x_293_;
v___y_275_ = v___x_297_;
goto v___jp_270_;
}
else
{
lean_object* v___x_298_; 
lean_dec(v___y_289_);
v___x_298_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
v___y_271_ = v___x_292_;
v___y_272_ = v___x_295_;
v___y_273_ = v___x_294_;
v___y_274_ = v___x_293_;
v___y_275_ = v___x_298_;
goto v___jp_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___boxed(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1(v_x_309_, v_a_310_, v_a_311_);
lean_dec_ref(v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Derive__eval__expr__instance__using__meta__eval____1(lean_object* v_x_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Derive__eval__expr__instance__using__meta__eval___00__closed__1));
lean_inc(v_x_335_);
v___x_340_ = l_Lean_Syntax_isOfKind(v_x_335_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_x_335_);
v___x_341_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_kind_345_; lean_object* v___x_346_; lean_object* v_tk_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v___x_366_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l_Lean_Syntax_getArg(v_x_335_, v___x_342_);
v___x_344_ = lean_unsigned_to_nat(1u);
v_kind_345_ = l_Lean_Syntax_getArg(v_x_335_, v___x_344_);
v___x_346_ = lean_unsigned_to_nat(2u);
v_tk_347_ = l_Lean_Syntax_getArg(v_x_335_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(3u);
v___x_349_ = l_Lean_Syntax_getArg(v_x_335_, v___x_348_);
lean_dec(v_x_335_);
v___x_366_ = l_Lean_Syntax_getOptional_x3f(v___x_343_);
lean_dec(v___x_343_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
v___y_351_ = v___x_367_;
goto v___jp_350_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_val_368_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_366_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v___x_366_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_val_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v___y_351_ = v___x_373_;
goto v___jp_350_;
}
}
}
v___jp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_box(0);
lean_inc(v___x_349_);
v___x_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_353_, 0, v___x_349_);
lean_closure_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__1___boxed), 9, 2);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_354_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(v___y_351_, v_kind_345_, v_tk_347_, v___x_349_, v_a_356_, v_a_336_, v_a_337_);
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v___y_351_);
lean_dec(v___x_349_);
lean_dec(v_tk_347_);
lean_dec(v_kind_345_);
v_a_358_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_355_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_355_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Derive__eval__expr__instance__using__meta__eval____1___boxed(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Derive__eval__expr__instance__using__meta__eval____1(v_x_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_380_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__2(void){
_start:
{
uint8_t v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = 0;
v___x_388_ = 1;
v___x_389_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1));
v___x_390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__0));
v___x_391_ = l_Lean_Parser_mkAntiquot(v___x_390_, v___x_389_, v___x_388_, v___x_387_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__4(void){
_start:
{
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = 0;
v___x_394_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__3));
v___x_395_ = l_Lean_Parser_nonReservedSymbol(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__6(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__5));
v___x_398_ = l_Lean_Parser_symbol(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__7(void){
_start:
{
uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_399_ = 1;
v___x_400_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__6, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__6);
v___x_401_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__5));
v___x_402_ = l_Lean_Parser_ident;
v___x_403_ = l_Lean_Parser_sepBy1(v___x_402_, v___x_401_, v___x_400_, v___x_399_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__8(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__7, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__7_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__7);
v___x_405_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__4, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__4);
v___x_406_ = l_Lean_Parser_andthen(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__9(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__8, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__8);
v___x_408_ = lean_unsigned_to_nat(1024u);
v___x_409_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1));
v___x_410_ = l_Lean_Parser_leadingNode(v___x_409_, v___x_408_, v___x_407_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__10(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__9, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__9_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__9);
v___x_412_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__2, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__2);
v___x_413_ = l_Lean_Parser_withAntiquot(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__11(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__10, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__10_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__10);
v___x_415_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1));
v___x_416_ = l_Lean_Parser_withCache(v___x_415_, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryOmit(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryOmit___closed__11, &l_Lean_Elab_ConfigEval_configEntryOmit___closed__11_once, _init_l_Lean_Elab_ConfigEval_configEntryOmit___closed__11);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2(void){
_start:
{
uint8_t v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_424_ = 0;
v___x_425_ = 1;
v___x_426_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1));
v___x_427_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0));
v___x_428_ = l_Lean_Parser_mkAntiquot(v___x_427_, v___x_426_, v___x_425_, v___x_424_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3));
v___x_431_ = l_Lean_Parser_checkNoWsBefore(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5));
v___x_434_ = l_Lean_Parser_symbol(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7));
v___x_437_ = l_Lean_Parser_symbol(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8);
v___x_439_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4);
v___x_440_ = l_Lean_Parser_andthen(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9);
v___x_442_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6);
v___x_443_ = l_Lean_Parser_andthen(v___x_442_, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10);
v___x_445_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4);
v___x_446_ = l_Lean_Parser_andthen(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11);
v___x_448_ = l_Lean_Parser_optional(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12);
v___x_450_ = l_Lean_Parser_ident;
v___x_451_ = l_Lean_Parser_andthen(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13);
v___x_453_ = lean_unsigned_to_nat(1024u);
v___x_454_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1));
v___x_455_ = l_Lean_Parser_leadingNode(v___x_454_, v___x_453_, v___x_452_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14);
v___x_457_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2);
v___x_458_ = l_Lean_Parser_withAntiquot(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__15);
v___x_460_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1));
v___x_461_ = l_Lean_Parser_withCache(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__16);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2(void){
_start:
{
uint8_t v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = 0;
v___x_470_ = 1;
v___x_471_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1));
v___x_472_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0));
v___x_473_ = l_Lean_Parser_mkAntiquot(v___x_472_, v___x_471_, v___x_470_, v___x_469_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8);
v___x_475_ = lean_unsigned_to_nat(1024u);
v___x_476_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1));
v___x_477_ = l_Lean_Parser_leadingNode(v___x_476_, v___x_475_, v___x_474_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__3);
v___x_479_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2);
v___x_480_ = l_Lean_Parser_withAntiquot(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__4);
v___x_482_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1));
v___x_483_ = l_Lean_Parser_withCache(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__5);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2(void){
_start:
{
uint8_t v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = 0;
v___x_492_ = 1;
v___x_493_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
v___x_494_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0));
v___x_495_ = l_Lean_Parser_mkAntiquot(v___x_494_, v___x_493_, v___x_492_, v___x_491_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard;
v___x_497_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix;
v___x_498_ = l_Lean_Parser_orelse(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3, &l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3);
v___x_500_ = lean_unsigned_to_nat(1024u);
v___x_501_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
v___x_502_ = l_Lean_Parser_leadingNode(v___x_501_, v___x_500_, v___x_499_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4);
v___x_504_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2);
v___x_505_ = l_Lean_Parser_withAntiquot(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5, &l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5);
v___x_507_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
v___x_508_ = l_Lean_Parser_withCache(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__6);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__2(void){
_start:
{
uint8_t v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_516_ = 0;
v___x_517_ = 1;
v___x_518_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
v___x_519_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__0));
v___x_520_ = l_Lean_Parser_mkAntiquot(v___x_519_, v___x_518_, v___x_517_, v___x_516_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__4(void){
_start:
{
uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = 0;
v___x_523_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__3));
v___x_524_ = l_Lean_Parser_nonReservedSymbol(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__6(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__5));
v___x_527_ = l_Lean_Parser_symbol(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__7(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_Parser_termParser(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__8(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__7, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__7_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__7);
v___x_531_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__6);
v___x_532_ = l_Lean_Parser_andthen(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__9(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__8, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__8);
v___x_534_ = l_Lean_Elab_ConfigEval_configEntryHandlerKey;
v___x_535_ = l_Lean_Parser_andthen(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__10(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__9, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__9);
v___x_537_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__4);
v___x_538_ = l_Lean_Parser_andthen(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__11(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__10, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__10_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__10);
v___x_540_ = lean_unsigned_to_nat(1024u);
v___x_541_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
v___x_542_ = l_Lean_Parser_leadingNode(v___x_541_, v___x_540_, v___x_539_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__12(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__11, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__11_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__11);
v___x_544_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__2);
v___x_545_ = l_Lean_Parser_withAntiquot(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__13(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__12, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__12_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__12);
v___x_547_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
v___x_548_ = l_Lean_Parser_withCache(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler___closed__13, &l_Lean_Elab_ConfigEval_configEntryHandler___closed__13_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler___closed__13);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry___closed__2(void){
_start:
{
uint8_t v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = 0;
v___x_557_ = 1;
v___x_558_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
v___x_559_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__0));
v___x_560_ = l_Lean_Parser_mkAntiquot(v___x_559_, v___x_558_, v___x_557_, v___x_556_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry___closed__3(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Elab_ConfigEval_configEntryHandler;
v___x_562_ = l_Lean_Elab_ConfigEval_configEntryOmit;
v___x_563_ = l_Lean_Parser_orelse(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry___closed__4(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry___closed__3, &l_Lean_Elab_ConfigEval_configEntry___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntry___closed__3);
v___x_565_ = lean_unsigned_to_nat(1024u);
v___x_566_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
v___x_567_ = l_Lean_Parser_leadingNode(v___x_566_, v___x_565_, v___x_564_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry___closed__5(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry___closed__4, &l_Lean_Elab_ConfigEval_configEntry___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntry___closed__4);
v___x_569_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry___closed__2, &l_Lean_Elab_ConfigEval_configEntry___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntry___closed__2);
v___x_570_ = l_Lean_Parser_withAntiquot(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry___closed__6(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry___closed__5, &l_Lean_Elab_ConfigEval_configEntry___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntry___closed__5);
v___x_572_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
v___x_573_ = l_Lean_Parser_withCache(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry___closed__6, &l_Lean_Elab_ConfigEval_configEntry___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntry___closed__6);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__2(void){
_start:
{
uint8_t v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_581_ = 0;
v___x_582_ = 1;
v___x_583_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_584_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__0));
v___x_585_ = l_Lean_Parser_mkAntiquot(v___x_584_, v___x_583_, v___x_582_, v___x_581_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__4(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__3));
v___x_588_ = l_Lean_Parser_symbol(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__6(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__5));
v___x_591_ = l_Lean_Parser_symbol(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__9(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_p_598_; 
v___x_595_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8);
v___x_596_ = l_Lean_Elab_ConfigEval_configEntry;
v___x_597_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__8));
v_p_598_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_597_, v___x_596_, v___x_595_);
return v_p_598_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__11(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__10));
v___x_601_ = l_Lean_Parser_checkColGe(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__12(void){
_start:
{
lean_object* v_p_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_p_602_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__9, &l_Lean_Elab_ConfigEval_configEntries___closed__9_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__9);
v___x_603_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__11, &l_Lean_Elab_ConfigEval_configEntries___closed__11_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__11);
v___x_604_ = l_Lean_Parser_andthen(v___x_603_, v_p_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__13(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__10));
v___x_606_ = l_Lean_Parser_checkColEq(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__15(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__14));
v___x_609_ = l_Lean_Parser_checkLinebreakBefore(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__16(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Parser_pushNone;
v___x_611_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__15, &l_Lean_Elab_ConfigEval_configEntries___closed__15_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__15);
v___x_612_ = l_Lean_Parser_andthen(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__17(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__16, &l_Lean_Elab_ConfigEval_configEntries___closed__16_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__16);
v___x_614_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__13, &l_Lean_Elab_ConfigEval_configEntries___closed__13_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__13);
v___x_615_ = l_Lean_Parser_andthen(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__18(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__17, &l_Lean_Elab_ConfigEval_configEntries___closed__17_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__17);
v___x_617_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__6, &l_Lean_Elab_ConfigEval_configEntries___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__6);
v___x_618_ = l_Lean_Parser_orelse(v___x_617_, v___x_616_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__19(void){
_start:
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_619_ = 1;
v___x_620_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__18, &l_Lean_Elab_ConfigEval_configEntries___closed__18_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__18);
v___x_621_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__5));
v___x_622_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__12, &l_Lean_Elab_ConfigEval_configEntries___closed__12_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__12);
v___x_623_ = l_Lean_Parser_sepBy(v___x_622_, v___x_621_, v___x_620_, v___x_619_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__20(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__19, &l_Lean_Elab_ConfigEval_configEntries___closed__19_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__19);
v___x_625_ = l_Lean_Parser_withPosition(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__21(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__20, &l_Lean_Elab_ConfigEval_configEntries___closed__20_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__20);
v___x_627_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__4, &l_Lean_Elab_ConfigEval_configEntries___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__4);
v___x_628_ = l_Lean_Parser_andthen(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__22(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__21, &l_Lean_Elab_ConfigEval_configEntries___closed__21_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__21);
v___x_630_ = lean_unsigned_to_nat(1024u);
v___x_631_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_632_ = l_Lean_Parser_leadingNode(v___x_631_, v___x_630_, v___x_629_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__23(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__22, &l_Lean_Elab_ConfigEval_configEntries___closed__22_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__22);
v___x_634_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__2, &l_Lean_Elab_ConfigEval_configEntries___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__2);
v___x_635_ = l_Lean_Parser_withAntiquot(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries___closed__24(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__23, &l_Lean_Elab_ConfigEval_configEntries___closed__23_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__23);
v___x_637_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_638_ = l_Lean_Parser_withCache(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries(void){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries___closed__24, &l_Lean_Elab_ConfigEval_configEntries___closed__24_once, _init_l_Lean_Elab_ConfigEval_configEntries___closed__24);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(size_t v_sz_640_, size_t v_i_641_, lean_object* v_bs_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_lt(v_i_641_, v_sz_640_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_bs_642_);
return v___x_644_;
}
else
{
lean_object* v_v_645_; lean_object* v___x_646_; lean_object* v_bs_x27_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_v_645_ = lean_array_uget(v_bs_642_, v_i_641_);
v___x_646_ = lean_unsigned_to_nat(0u);
v_bs_x27_647_ = lean_array_uset(v_bs_642_, v_i_641_, v___x_646_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_641_, v___x_648_);
v___x_650_ = lean_array_uset(v_bs_x27_647_, v_i_641_, v_v_645_);
v_i_641_ = v___x_649_;
v_bs_642_ = v___x_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(lean_object* v_sz_652_, lean_object* v_i_653_, lean_object* v_bs_654_){
_start:
{
size_t v_sz_boxed_655_; size_t v_i_boxed_656_; lean_object* v_res_657_; 
v_sz_boxed_655_ = lean_unbox_usize(v_sz_652_);
lean_dec(v_sz_652_);
v_i_boxed_656_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_boxed_655_, v_i_boxed_656_, v_bs_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(size_t v_sz_658_, size_t v_i_659_, lean_object* v_bs_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_661_ == 0)
{
return v_bs_660_;
}
else
{
lean_object* v_v_662_; lean_object* v___x_663_; lean_object* v_bs_x27_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v_v_662_ = lean_array_uget(v_bs_660_, v_i_659_);
v___x_663_ = lean_unsigned_to_nat(0u);
v_bs_x27_664_ = lean_array_uset(v_bs_660_, v_i_659_, v___x_663_);
v___x_665_ = l_Lean_TSyntax_getId(v_v_662_);
v___x_666_ = lean_erase_macro_scopes(v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_v_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_659_, v___x_668_);
v___x_670_ = lean_array_uset(v_bs_x27_664_, v_i_659_, v___x_667_);
v_i_659_ = v___x_669_;
v_bs_660_ = v___x_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(lean_object* v_sz_672_, lean_object* v_i_673_, lean_object* v_bs_674_){
_start:
{
size_t v_sz_boxed_675_; size_t v_i_boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_675_ = lean_unbox_usize(v_sz_672_);
lean_dec(v_sz_672_);
v_i_boxed_676_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_boxed_675_, v_i_boxed_676_, v_bs_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(uint8_t v___x_678_, lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___y_684_; uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_688_ == 0)
{
lean_object* v_fst_689_; uint8_t v___x_690_; 
v_fst_689_ = lean_ctor_get(v_b_682_, 0);
v___x_690_ = lean_unbox(v_fst_689_);
if (v___x_690_ == 0)
{
lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_snd_691_ = lean_ctor_get(v_b_682_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_b_682_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_b_682_, 0);
lean_dec(v_unused_700_);
v___x_693_ = v_b_682_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_dec(v_b_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_box(v___x_678_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_691_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v___y_684_ = v___x_697_;
goto v___jp_683_;
}
}
}
else
{
lean_object* v_snd_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_snd_701_ = lean_ctor_get(v_b_682_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_682_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_b_682_, 0);
lean_dec(v_unused_712_);
v___x_703_ = v_b_682_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snd_701_);
lean_dec(v_b_682_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
lean_inc(v___x_705_);
v___x_706_ = lean_array_push(v_snd_701_, v___x_705_);
v___x_707_ = lean_box(v___x_688_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_706_);
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_706_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_684_ = v___x_709_;
goto v___jp_683_;
}
}
}
}
else
{
return v_b_682_;
}
v___jp_683_:
{
size_t v___x_685_; size_t v___x_686_; 
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_i_680_, v___x_685_);
v_i_680_ = v___x_686_;
v_b_682_ = v___y_684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(lean_object* v___x_713_, lean_object* v_as_714_, lean_object* v_i_715_, lean_object* v_stop_716_, lean_object* v_b_717_){
_start:
{
uint8_t v___x_8515__boxed_718_; size_t v_i_boxed_719_; size_t v_stop_boxed_720_; lean_object* v_res_721_; 
v___x_8515__boxed_718_ = lean_unbox(v___x_713_);
v_i_boxed_719_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_stop_boxed_720_ = lean_unbox_usize(v_stop_716_);
lean_dec(v_stop_716_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_8515__boxed_718_, v_as_714_, v_i_boxed_719_, v_stop_boxed_720_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(lean_object* v_as_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_b_728_){
_start:
{
lean_object* v_a_731_; uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_lt(v_i_727_, v_sz_726_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_b_728_);
return v___x_736_;
}
else
{
lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_899_; 
v_fst_737_ = lean_ctor_get(v_b_728_, 0);
v_snd_738_ = lean_ctor_get(v_b_728_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_b_728_);
if (v_isSharedCheck_899_ == 0)
{
v___x_740_ = v_b_728_;
v_isShared_741_ = v_isSharedCheck_899_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_inc(v_fst_737_);
lean_dec(v_b_728_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_899_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___y_743_; lean_object* v_a_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_a_766_ = lean_array_uget_borrowed(v_as_725_, v_i_727_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
lean_inc(v_a_766_);
v___x_768_ = l_Lean_Syntax_isOfKind(v_a_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_del_object(v___x_740_);
v___x_769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_769_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_737_);
lean_ctor_set(v___x_770_, 1, v_snd_738_);
v_a_731_ = v___x_770_;
goto v___jp_730_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_771_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = l_Lean_Syntax_getArg(v_a_766_, v___x_779_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1));
lean_inc(v___x_781_);
v___x_783_ = l_Lean_Syntax_isOfKind(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
lean_del_object(v___x_740_);
v___x_784_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
lean_inc(v___x_781_);
v___x_785_ = l_Lean_Syntax_isOfKind(v___x_781_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v___x_781_);
v___x_786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v___x_786_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_737_);
lean_ctor_set(v___x_787_, 1, v_snd_738_);
v_a_731_ = v___x_787_;
goto v___jp_730_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_788_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_786_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Lean_Syntax_getArg(v___x_781_, v___x_780_);
v___x_797_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
lean_inc(v___x_796_);
v___x_798_ = l_Lean_Syntax_isOfKind(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v___x_796_);
lean_dec(v___x_781_);
v___x_799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v___x_799_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_737_);
lean_ctor_set(v___x_800_, 1, v_snd_738_);
v_a_731_ = v___x_800_;
goto v___jp_730_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_fst_812_; uint8_t v_snd_813_; lean_object* v_____x_819_; 
v___x_809_ = lean_unsigned_to_nat(3u);
v___x_810_ = l_Lean_Syntax_getArg(v___x_781_, v___x_809_);
lean_dec(v___x_781_);
if (v___x_798_ == 0)
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref(v___x_823_);
v_____x_819_ = v_a_824_;
goto v___jp_818_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v___x_810_);
lean_dec(v___x_796_);
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_825_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_823_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = l_Lean_Syntax_getArg(v___x_796_, v___x_779_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1));
lean_inc(v___x_833_);
v___x_835_ = l_Lean_Syntax_isOfKind(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1));
v___x_837_ = l_Lean_Syntax_isOfKind(v___x_833_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v_____x_819_ = v_a_839_;
goto v___jp_818_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v___x_810_);
lean_dec(v___x_796_);
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_840_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_box(0);
v___x_849_ = 1;
v_fst_812_ = v___x_848_;
v_snd_813_ = v___x_849_;
goto v___jp_811_;
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = l_Lean_Syntax_getArg(v___x_833_, v___x_779_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v___x_850_);
v___x_852_ = l_Lean_Syntax_isOfKind(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_dec(v___x_850_);
lean_dec(v___x_833_);
v___x_853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref(v___x_853_);
v_____x_819_ = v_a_854_;
goto v___jp_818_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v___x_810_);
lean_dec(v___x_796_);
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_855_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_853_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = l_Lean_Syntax_getArg(v___x_833_, v___x_780_);
lean_dec(v___x_833_);
lean_inc(v___x_863_);
v___x_864_ = l_Lean_Syntax_matchesNull(v___x_863_, v___x_779_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(2u);
v___x_866_ = l_Lean_Syntax_matchesNull(v___x_863_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec(v___x_850_);
v___x_867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v_____x_819_ = v_a_868_;
goto v___jp_818_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v___x_810_);
lean_dec(v___x_796_);
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_869_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_867_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = l_Lean_TSyntax_getId(v___x_850_);
lean_dec(v___x_850_);
v___x_878_ = lean_erase_macro_scopes(v___x_877_);
v___x_879_ = 1;
v_fst_812_ = v___x_878_;
v_snd_813_ = v___x_879_;
goto v___jp_811_;
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
lean_dec(v___x_863_);
v___x_880_ = l_Lean_TSyntax_getId(v___x_850_);
lean_dec(v___x_850_);
v___x_881_ = lean_erase_macro_scopes(v___x_880_);
v___x_882_ = 0;
v_fst_812_ = v___x_881_;
v_snd_813_ = v___x_882_;
goto v___jp_811_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_815_, 0, v___x_796_);
lean_ctor_set(v___x_815_, 1, v_fst_812_);
lean_ctor_set(v___x_815_, 2, v___x_810_);
lean_ctor_set(v___x_815_, 3, v___x_814_);
lean_ctor_set(v___x_815_, 4, v___x_814_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*5, v_snd_813_);
v___x_816_ = lean_array_push(v_snd_738_, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_737_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v_a_731_ = v___x_817_;
goto v___jp_730_;
}
v___jp_818_:
{
lean_object* v_fst_820_; lean_object* v_snd_821_; uint8_t v___x_822_; 
v_fst_820_ = lean_ctor_get(v_____x_819_, 0);
lean_inc(v_fst_820_);
v_snd_821_ = lean_ctor_get(v_____x_819_, 1);
lean_inc(v_snd_821_);
lean_dec_ref(v_____x_819_);
v___x_822_ = lean_unbox(v_snd_821_);
lean_dec(v_snd_821_);
v_fst_812_ = v_fst_820_;
v_snd_813_ = v___x_822_;
goto v___jp_811_;
}
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_883_ = l_Lean_Syntax_getArg(v___x_781_, v___x_780_);
lean_dec(v___x_781_);
v___x_884_ = l_Lean_Syntax_getArgs(v___x_883_);
lean_dec(v___x_883_);
v___x_885_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
v___x_886_ = lean_array_get_size(v___x_884_);
v___x_887_ = lean_nat_dec_lt(v___x_779_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec_ref(v___x_884_);
v___y_743_ = v___x_885_;
goto v___jp_742_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_box(v___x_783_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_885_);
v___x_890_ = lean_nat_dec_le(v___x_886_, v___x_886_);
if (v___x_890_ == 0)
{
if (v___x_887_ == 0)
{
lean_dec_ref(v___x_889_);
lean_dec_ref(v___x_884_);
v___y_743_ = v___x_885_;
goto v___jp_742_;
}
else
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; lean_object* v_snd_894_; 
v___x_891_ = ((size_t)0ULL);
v___x_892_ = lean_usize_of_nat(v___x_886_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_783_, v___x_884_, v___x_891_, v___x_892_, v___x_889_);
lean_dec_ref(v___x_884_);
v_snd_894_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_snd_894_);
lean_dec_ref(v___x_893_);
v___y_743_ = v_snd_894_;
goto v___jp_742_;
}
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; lean_object* v_snd_898_; 
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_886_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_783_, v___x_884_, v___x_895_, v___x_896_, v___x_889_);
lean_dec_ref(v___x_884_);
v_snd_898_ = lean_ctor_get(v___x_897_, 1);
lean_inc(v_snd_898_);
lean_dec_ref(v___x_897_);
v___y_743_ = v_snd_898_;
goto v___jp_742_;
}
}
}
}
v___jp_742_:
{
size_t v_sz_744_; size_t v___x_745_; lean_object* v___x_746_; 
v_sz_744_ = lean_array_size(v___y_743_);
v___x_745_ = ((size_t)0ULL);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_744_, v___x_745_, v___y_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_749_; 
lean_dec_ref(v___x_747_);
if (v_isShared_741_ == 0)
{
v___x_749_ = v___x_740_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_737_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_738_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v_a_731_ = v___x_749_;
goto v___jp_730_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_del_object(v___x_740_);
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v_a_751_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_747_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_747_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_val_759_; size_t v_sz_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v_val_759_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_746_);
v_sz_760_ = lean_array_size(v_val_759_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_760_, v___x_745_, v_val_759_);
v___x_762_ = l_Array_append___redArg(v_fst_737_, v___x_761_);
lean_dec_ref(v___x_761_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_762_);
v___x_764_ = v___x_740_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_738_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v_a_731_ = v___x_764_;
goto v___jp_730_;
}
}
}
}
}
v___jp_730_:
{
size_t v___x_732_; size_t v___x_733_; 
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_727_, v___x_732_);
v_i_727_ = v___x_733_;
v_b_728_ = v_a_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object* v_as_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_){
_start:
{
size_t v_sz_boxed_905_; size_t v_i_boxed_906_; lean_object* v_res_907_; 
v_sz_boxed_905_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_906_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_900_, v_sz_boxed_905_, v_i_boxed_906_, v_b_903_);
lean_dec_ref(v_as_900_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t v_sz_908_, size_t v_i_909_, lean_object* v_bs_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_bs_910_);
return v___x_912_;
}
else
{
lean_object* v_v_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_v_913_ = lean_array_uget(v_bs_910_, v_i_909_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
lean_inc(v_v_913_);
v___x_915_ = l_Lean_Syntax_isOfKind(v_v_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v_v_913_);
lean_dec_ref(v_bs_910_);
v___x_916_ = lean_box(0);
return v___x_916_;
}
else
{
lean_object* v___x_917_; lean_object* v_bs_x27_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
v___x_917_ = lean_unsigned_to_nat(0u);
v_bs_x27_918_ = lean_array_uset(v_bs_910_, v_i_909_, v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_909_, v___x_919_);
v___x_921_ = lean_array_uset(v_bs_x27_918_, v_i_909_, v_v_913_);
v_i_909_ = v___x_920_;
v_bs_910_ = v___x_921_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_bs_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_927_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_boxed_926_, v_i_boxed_927_, v_bs_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object* v_entries_x3f_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_omitFields_938_; lean_object* v_handlers_939_; lean_object* v___x_942_; lean_object* v_omitFields_943_; lean_object* v___y_945_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v_omitFields_943_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0));
if (lean_obj_tag(v_entries_x3f_933_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_val_973_ = lean_ctor_get(v_entries_x3f_933_, 0);
lean_inc_n(v_val_973_, 2);
lean_dec_ref(v_entries_x3f_933_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_975_ = l_Lean_Syntax_isOfKind(v_val_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_val_973_);
v___x_976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = l_Lean_Syntax_getArg(v_val_973_, v___x_985_);
lean_dec(v_val_973_);
v___x_987_ = l_Lean_Syntax_getArgs(v___x_986_);
lean_dec(v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
v___x_989_ = lean_array_get_size(v___x_987_);
v___x_990_ = lean_nat_dec_lt(v___x_942_, v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_987_);
v___y_945_ = v___x_988_;
goto v___jp_944_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_991_ = lean_box(v___x_975_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_988_);
v___x_993_ = lean_nat_dec_le(v___x_989_, v___x_989_);
if (v___x_993_ == 0)
{
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_987_);
v___y_945_ = v___x_988_;
goto v___jp_944_;
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; lean_object* v_snd_997_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_989_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_975_, v___x_987_, v___x_994_, v___x_995_, v___x_992_);
lean_dec_ref(v___x_987_);
v_snd_997_ = lean_ctor_get(v___x_996_, 1);
lean_inc(v_snd_997_);
lean_dec_ref(v___x_996_);
v___y_945_ = v_snd_997_;
goto v___jp_944_;
}
}
else
{
size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; lean_object* v_snd_1001_; 
v___x_998_ = ((size_t)0ULL);
v___x_999_ = lean_usize_of_nat(v___x_989_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_975_, v___x_987_, v___x_998_, v___x_999_, v___x_992_);
lean_dec_ref(v___x_987_);
v_snd_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_1000_);
v___y_945_ = v_snd_1001_;
goto v___jp_944_;
}
}
}
}
else
{
lean_dec(v_entries_x3f_933_);
v_omitFields_938_ = v_omitFields_943_;
v_handlers_939_ = v_omitFields_943_;
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_omitFields_938_);
lean_ctor_set(v___x_940_, 1, v_handlers_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
v___jp_944_:
{
size_t v_sz_946_; size_t v___x_947_; lean_object* v___x_948_; 
v_sz_946_ = lean_array_size(v___y_945_);
v___x_947_ = ((size_t)0ULL);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_946_, v___x_947_, v___y_945_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v___x_949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_val_958_; lean_object* v___x_959_; size_t v_sz_960_; lean_object* v___x_961_; 
v_val_958_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v___x_948_);
v___x_959_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1));
v_sz_960_ = lean_array_size(v_val_958_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_val_958_, v_sz_960_, v___x_947_, v___x_959_);
lean_dec(v_val_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v_fst_963_; lean_object* v_snd_964_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v_fst_963_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_fst_963_);
v_snd_964_ = lean_ctor_get(v_a_962_, 1);
lean_inc(v_snd_964_);
lean_dec(v_a_962_);
v_omitFields_938_ = v_fst_963_;
v_handlers_939_ = v_snd_964_;
goto v___jp_937_;
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_961_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object* v_entries_x3f_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object* v_as_1007_, size_t v_sz_1008_, size_t v_i_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_1007_, v_sz_1008_, v_i_1009_, v_b_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object* v_as_1015_, lean_object* v_sz_1016_, lean_object* v_i_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1016_);
lean_dec(v_sz_1016_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_1015_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_as_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter(lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__0));
v___x_1133_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit_formatter___closed__6));
v___x_1134_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1132_, v___x_1133_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_formatter___boxed(lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_ConfigEval_configEntryOmit_formatter(v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0(lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0___boxed(lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___lam__0(v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter(lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__1));
v___x_1189_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___closed__9));
v___x_1190_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1188_, v___x_1189_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___boxed(lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter(v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter(lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__0));
v___x_1214_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___closed__1));
v___x_1215_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1213_, v___x_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___boxed(lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter(v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
return v_res_1221_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_formatter___boxed), 5, 0);
v___x_1230_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_formatter___boxed), 5, 0);
v___x_1231_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1231_, 0, v___x_1230_);
lean_closure_set(v___x_1231_, 1, v___x_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1, &l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__1);
v___x_1233_ = lean_unsigned_to_nat(1024u);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
v___x_1235_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1235_, 0, v___x_1234_);
lean_closure_set(v___x_1235_, 1, v___x_1233_);
lean_closure_set(v___x_1235_, 2, v___x_1232_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__0));
v___x_1242_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___closed__2);
v___x_1243_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1241_, v___x_1242_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___boxed(lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter(v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
return v_res_1249_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__4));
v___x_1269_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey_formatter___boxed), 5, 0);
v___x_1270_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1270_, 0, v___x_1269_);
lean_closure_set(v___x_1270_, 1, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5, &l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__5);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__1));
v___x_1273_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1273_, 0, v___x_1272_);
lean_closure_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__6);
v___x_1275_ = lean_unsigned_to_nat(1024u);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
v___x_1277_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1277_, 0, v___x_1276_);
lean_closure_set(v___x_1277_, 1, v___x_1275_);
lean_closure_set(v___x_1277_, 2, v___x_1274_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter(lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__0));
v___x_1284_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7, &l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_formatter___closed__7);
v___x_1285_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1283_, v___x_1284_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_formatter___boxed(lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Elab_ConfigEval_configEntryHandler_formatter(v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
return v_res_1291_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandler_formatter___boxed), 5, 0);
v___x_1300_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryOmit_formatter___boxed), 5, 0);
v___x_1301_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1301_, 0, v___x_1300_);
lean_closure_set(v___x_1301_, 1, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1, &l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1_once, _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__1);
v___x_1303_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2, &l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__2);
v___x_1305_ = lean_unsigned_to_nat(1024u);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
v___x_1307_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1307_, 0, v___x_1306_);
lean_closure_set(v___x_1307_, 1, v___x_1305_);
lean_closure_set(v___x_1307_, 2, v___x_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry_formatter___closed__0));
v___x_1314_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3, &l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntry_formatter___closed__3);
v___x_1315_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1313_, v___x_1314_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_formatter___boxed(lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_ConfigEval_configEntry_formatter(v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_formatter___closed__2));
v___x_1334_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__5));
v___x_1335_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntry_formatter___boxed), 5, 0);
v___x_1336_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_formatter___boxed), 8, 3);
lean_closure_set(v___x_1336_, 0, v___x_1335_);
lean_closure_set(v___x_1336_, 1, v___x_1334_);
lean_closure_set(v___x_1336_, 2, v___x_1333_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3, &l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__3);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_formatter___closed__1));
v___x_1339_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1339_, 0, v___x_1338_);
lean_closure_set(v___x_1339_, 1, v___x_1337_);
return v___x_1339_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4, &l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__4);
v___x_1341_ = lean_unsigned_to_nat(1024u);
v___x_1342_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_1343_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1343_, 0, v___x_1342_);
lean_closure_set(v___x_1343_, 1, v___x_1341_);
lean_closure_set(v___x_1343_, 2, v___x_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter(lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_formatter___closed__0));
v___x_1350_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5, &l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntries_formatter___closed__5);
v___x_1351_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1349_, v___x_1350_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_formatter___boxed(lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Elab_ConfigEval_configEntries_formatter(v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer(lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__0));
v___x_1391_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__6));
v___x_1392_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1390_, v___x_1391_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___boxed(lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer(v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1398_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__2));
v___x_1411_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_1412_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1412_, 0, v___x_1411_);
lean_closure_set(v___x_1412_, 1, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__3);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__1));
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1415_, 0, v___x_1414_);
lean_closure_set(v___x_1415_, 1, v___x_1413_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__4);
v___x_1417_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_1418_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1418_, 0, v___x_1417_);
lean_closure_set(v___x_1418_, 1, v___x_1416_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__5);
v___x_1420_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__6);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___closed__2));
v___x_1423_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1423_, 0, v___x_1422_);
lean_closure_set(v___x_1423_, 1, v___x_1421_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__7);
v___x_1425_ = lean_unsigned_to_nat(1024u);
v___x_1426_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1));
v___x_1427_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1427_, 0, v___x_1426_);
lean_closure_set(v___x_1427_, 1, v___x_1425_);
lean_closure_set(v___x_1427_, 2, v___x_1424_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer(lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__0));
v___x_1434_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8, &l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___closed__8);
v___x_1435_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1433_, v___x_1434_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___boxed(lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer(v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer(lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__0));
v___x_1459_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___closed__1));
v___x_1460_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1458_, v___x_1459_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___boxed(lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer(v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1466_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard_parenthesizer___boxed), 5, 0);
v___x_1475_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix_parenthesizer___boxed), 5, 0);
v___x_1476_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1476_, 0, v___x_1475_);
lean_closure_set(v___x_1476_, 1, v___x_1474_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1, &l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__1);
v___x_1478_ = lean_unsigned_to_nat(1024u);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1));
v___x_1480_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1480_, 0, v___x_1479_);
lean_closure_set(v___x_1480_, 1, v___x_1478_);
lean_closure_set(v___x_1480_, 2, v___x_1477_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer(lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__0));
v___x_1487_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2, &l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___closed__2);
v___x_1488_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1486_, v___x_1487_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___boxed(lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer(v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1494_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__4));
v___x_1514_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandlerKey_parenthesizer___boxed), 5, 0);
v___x_1515_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1515_, 0, v___x_1514_);
lean_closure_set(v___x_1515_, 1, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5, &l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__5);
v___x_1517_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__1));
v___x_1518_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1518_, 0, v___x_1517_);
lean_closure_set(v___x_1518_, 1, v___x_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6, &l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__6);
v___x_1520_ = lean_unsigned_to_nat(1024u);
v___x_1521_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1));
v___x_1522_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1522_, 0, v___x_1521_);
lean_closure_set(v___x_1522_, 1, v___x_1520_);
lean_closure_set(v___x_1522_, 2, v___x_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer(lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__0));
v___x_1529_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7, &l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7_once, _init_l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___closed__7);
v___x_1530_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1528_, v___x_1529_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___boxed(lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer(v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
return v_res_1536_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryHandler_parenthesizer___boxed), 5, 0);
v___x_1545_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntryOmit_parenthesizer___boxed), 5, 0);
v___x_1546_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1546_, 0, v___x_1545_);
lean_closure_set(v___x_1546_, 1, v___x_1544_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1, &l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1_once, _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__1);
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1549_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2, &l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2_once, _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__2);
v___x_1550_ = lean_unsigned_to_nat(1024u);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry___closed__1));
v___x_1552_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1552_, 0, v___x_1551_);
lean_closure_set(v___x_1552_, 1, v___x_1550_);
lean_closure_set(v___x_1552_, 2, v___x_1549_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer(lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__0));
v___x_1559_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3, &l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntry_parenthesizer___closed__3);
v___x_1560_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1558_, v___x_1559_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntry_parenthesizer___boxed(lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_ConfigEval_configEntry_parenthesizer(v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1566_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = 1;
v___x_1579_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__2));
v___x_1580_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__5));
v___x_1581_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_configEntry_parenthesizer___boxed), 5, 0);
v___x_1582_ = lean_box(v___x_1578_);
v___x_1583_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1583_, 0, v___x_1581_);
lean_closure_set(v___x_1583_, 1, v___x_1580_);
lean_closure_set(v___x_1583_, 2, v___x_1579_);
lean_closure_set(v___x_1583_, 3, v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3, &l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3_once, _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__3);
v___x_1585_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__1));
v___x_1586_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1586_, 0, v___x_1585_);
lean_closure_set(v___x_1586_, 1, v___x_1584_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1587_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4, &l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4_once, _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__4);
v___x_1588_ = lean_unsigned_to_nat(1024u);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries___closed__1));
v___x_1590_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1590_, 0, v___x_1589_);
lean_closure_set(v___x_1590_, 1, v___x_1588_);
lean_closure_set(v___x_1590_, 2, v___x_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer(lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__0));
v___x_1597_ = lean_obj_once(&l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5, &l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5_once, _init_l_Lean_Elab_ConfigEval_configEntries_parenthesizer___closed__5);
v___x_1598_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1596_, v___x_1597_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_configEntries_parenthesizer___boxed(lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Elab_ConfigEval_configEntries_parenthesizer(v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__defEvalConfigItemCmd__1(lean_object* v_x_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1));
lean_inc(v_x_1605_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_x_1605_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec(v_x_1605_);
v___x_1611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__instance____1_spec__0___redArg();
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_kind_1617_; lean_object* v___x_1618_; lean_object* v_tk_1619_; lean_object* v___x_1620_; lean_object* v_fn_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_struct_1625_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1657_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1612_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1614_);
v___x_1616_ = lean_unsigned_to_nat(2u);
v_kind_1617_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1616_);
v___x_1618_ = lean_unsigned_to_nat(3u);
v_tk_1619_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1618_);
v___x_1620_ = lean_unsigned_to_nat(4u);
v_fn_1621_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1620_);
v___x_1622_ = lean_unsigned_to_nat(5u);
v___x_1623_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1622_);
v___x_1624_ = lean_unsigned_to_nat(7u);
v_struct_1625_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1624_);
v___x_1669_ = lean_unsigned_to_nat(8u);
v___x_1670_ = l_Lean_Syntax_getArg(v_x_1605_, v___x_1669_);
lean_dec(v_x_1605_);
v___x_1671_ = l_Lean_Syntax_getOptional_x3f(v___x_1670_);
lean_dec(v___x_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(0);
v___y_1657_ = v___x_1672_;
goto v___jp_1656_;
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_val_1673_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1671_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_dec(v___x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_val_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v___y_1657_ = v___x_1678_;
goto v___jp_1656_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v___y_1629_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_Lean_Elab_ConfigEval_defEvalConfigItem(v___y_1630_, v___y_1627_, v_kind_1617_, v_tk_1619_, v_struct_1625_, v_fn_1621_, v___y_1628_, v_a_1632_, v_a_1606_, v_a_1607_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec(v_struct_1625_);
lean_dec(v_fn_1621_);
lean_dec(v_tk_1619_);
lean_dec(v_kind_1617_);
v_a_1634_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1631_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1631_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
v___jp_1642_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Syntax_getOptional_x3f(v___x_1613_);
lean_dec(v___x_1613_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_box(0);
v___y_1627_ = v___y_1645_;
v___y_1628_ = v___y_1643_;
v___y_1629_ = v___y_1644_;
v___y_1630_ = v___x_1647_;
goto v___jp_1626_;
}
else
{
lean_object* v_val_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_val_1648_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1646_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_val_1648_);
lean_dec(v___x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1627_ = v___y_1645_;
v___y_1628_ = v___y_1643_;
v___y_1629_ = v___y_1644_;
v___y_1630_ = v___x_1653_;
goto v___jp_1626_;
}
}
}
}
v___jp_1656_:
{
lean_object* v_binders_1658_; lean_object* v___x_1659_; 
v_binders_1658_ = l_Lean_Syntax_getArgs(v___x_1623_);
lean_dec(v___x_1623_);
v___x_1659_ = l_Lean_Syntax_getOptional_x3f(v___x_1615_);
lean_dec(v___x_1615_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_box(0);
v___y_1643_ = v_binders_1658_;
v___y_1644_ = v___y_1657_;
v___y_1645_ = v___x_1660_;
goto v___jp_1642_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_val_1661_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
v___y_1643_ = v_binders_1658_;
v___y_1644_ = v___y_1657_;
v___y_1645_ = v___x_1666_;
goto v___jp_1642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__defEvalConfigItemCmd__1___boxed(lean_object* v_x_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______elabRules__Lean__Elab__ConfigEval__defEvalConfigItemCmd__1(v_x_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_1692_ = lean_unsigned_to_nat(2u);
v___x_1693_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_1691_, v___x_1692_, v_a_1687_, v_a_1688_, v_a_1689_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed), 4, 0);
v___x_1700_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((lean_object*)(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1));
v___x_1703_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0);
v___x_1704_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_1702_, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t v_sz_1707_, size_t v_i_1708_, lean_object* v_bs_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
if (v___x_1710_ == 0)
{
return v_bs_1709_;
}
else
{
lean_object* v_v_1711_; lean_object* v___x_1712_; lean_object* v_bs_x27_1713_; size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v_v_1711_ = lean_array_uget(v_bs_1709_, v_i_1708_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v_bs_x27_1713_ = lean_array_uset(v_bs_1709_, v_i_1708_, v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1708_, v___x_1714_);
v___x_1716_ = lean_array_uset(v_bs_x27_1713_, v_i_1708_, v_v_1711_);
v_i_1708_ = v___x_1715_;
v_bs_1709_ = v___x_1716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object* v_sz_1718_, lean_object* v_i_1719_, lean_object* v_bs_1720_){
_start:
{
size_t v_sz_boxed_1721_; size_t v_i_boxed_1722_; lean_object* v_res_1723_; 
v_sz_boxed_1721_ = lean_unbox_usize(v_sz_1718_);
lean_dec(v_sz_1718_);
v_i_boxed_1722_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_boxed_1721_, v_i_boxed_1722_, v_bs_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object* v_stx_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3));
lean_inc(v_stx_1751_);
v___x_1755_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5));
lean_inc(v_stx_1751_);
v___x_1757_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7));
lean_inc(v_stx_1751_);
v___x_1759_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__9));
lean_inc(v_stx_1751_);
v___x_1761_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1763_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1762_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1765_);
v___x_1767_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1766_);
v___x_1768_ = l_Lean_Syntax_matchesNull(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1766_, v___x_1764_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1771_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1770_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = l_Lean_mkHole(v_stx_1751_, v___x_1768_);
lean_dec(v_stx_1751_);
v___x_1773_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1774_ = lean_array_push(v___x_1773_, v___x_1772_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v_a_1753_);
return v___x_1775_;
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = l_Lean_Syntax_getArg(v___x_1766_, v___x_1764_);
lean_dec(v___x_1766_);
v___x_1777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v___x_1776_);
v___x_1778_ = l_Lean_Syntax_isOfKind(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v___x_1776_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1780_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1779_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v_stx_1751_);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1782_ = lean_array_push(v___x_1781_, v___x_1776_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1753_);
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_unsigned_to_nat(2u);
v___x_1785_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_matchesNull(v___x_1785_, v___x_1784_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1788_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1787_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_ids_1791_; size_t v_sz_1792_; size_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1789_);
lean_dec(v_stx_1751_);
v_ids_1791_ = l_Lean_Syntax_getArgs(v___x_1790_);
lean_dec(v___x_1790_);
v_sz_1792_ = lean_array_size(v_ids_1791_);
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1792_, v___x_1793_, v_ids_1791_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_a_1753_);
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___y_1799_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1796_);
v___x_1805_ = lean_unsigned_to_nat(2u);
v___x_1806_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1805_);
v___x_1807_ = l_Lean_Syntax_isNone(v___x_1806_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Syntax_matchesNull(v___x_1806_, v___x_1805_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1797_);
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1810_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1809_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1810_;
}
else
{
lean_dec(v_stx_1751_);
v___y_1799_ = v_a_1753_;
goto v___jp_1798_;
}
}
else
{
lean_dec(v___x_1806_);
lean_dec(v_stx_1751_);
v___y_1799_ = v_a_1753_;
goto v___jp_1798_;
}
v___jp_1798_:
{
lean_object* v_ids_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_ids_1800_ = l_Lean_Syntax_getArgs(v___x_1797_);
lean_dec(v___x_1797_);
v_sz_1801_ = lean_array_size(v_ids_1800_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1801_, v___x_1802_, v_ids_1800_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___y_1799_);
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___y_1814_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1812_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1811_);
v___x_1820_ = lean_unsigned_to_nat(2u);
v___x_1821_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_isNone(v___x_1821_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = l_Lean_Syntax_matchesNull(v___x_1821_, v___x_1820_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1812_);
v___x_1824_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__10));
v___x_1825_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1751_, v___x_1824_, v_a_1752_, v_a_1753_);
lean_dec(v_stx_1751_);
return v___x_1825_;
}
else
{
lean_dec(v_stx_1751_);
v___y_1814_ = v_a_1753_;
goto v___jp_1813_;
}
}
else
{
lean_dec(v___x_1821_);
lean_dec(v_stx_1751_);
v___y_1814_ = v_a_1753_;
goto v___jp_1813_;
}
v___jp_1813_:
{
lean_object* v_ids_1815_; size_t v_sz_1816_; size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_ids_1815_ = l_Lean_Syntax_getArgs(v___x_1812_);
lean_dec(v___x_1812_);
v_sz_1816_ = lean_array_size(v_ids_1815_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1816_, v___x_1817_, v_ids_1815_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___y_1814_);
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object* v_stx_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v_stx_1826_, v_a_1827_, v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t v_sz_1830_, size_t v_i_1831_, lean_object* v_bs_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_lt(v_i_1831_, v_sz_1830_);
if (v___x_1833_ == 0)
{
return v_bs_1832_;
}
else
{
lean_object* v_v_1834_; lean_object* v___x_1835_; lean_object* v_bs_x27_1836_; size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v_v_1834_ = lean_array_uget(v_bs_1832_, v_i_1831_);
v___x_1835_ = lean_unsigned_to_nat(0u);
v_bs_x27_1836_ = lean_array_uset(v_bs_1832_, v_i_1831_, v___x_1835_);
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1831_, v___x_1837_);
v___x_1839_ = lean_array_uset(v_bs_x27_1836_, v_i_1831_, v_v_1834_);
v_i_1831_ = v___x_1838_;
v_bs_1832_ = v___x_1839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object* v_sz_1841_, lean_object* v_i_1842_, lean_object* v_bs_1843_){
_start:
{
size_t v_sz_boxed_1844_; size_t v_i_boxed_1845_; lean_object* v_res_1846_; 
v_sz_boxed_1844_ = lean_unbox_usize(v_sz_1841_);
lean_dec(v_sz_1841_);
v_i_boxed_1845_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_boxed_1844_, v_i_boxed_1845_, v_bs_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t v_sz_1847_, size_t v_i_1848_, lean_object* v_bs_1849_){
_start:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_usize_dec_lt(v_i_1848_, v_sz_1847_);
if (v___x_1850_ == 0)
{
return v_bs_1849_;
}
else
{
lean_object* v_v_1851_; lean_object* v___x_1852_; lean_object* v_bs_x27_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v_v_1851_ = lean_array_uget(v_bs_1849_, v_i_1848_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v_bs_x27_1853_ = lean_array_uset(v_bs_1849_, v_i_1848_, v___x_1852_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1848_, v___x_1854_);
v___x_1856_ = lean_array_uset(v_bs_x27_1853_, v_i_1848_, v_v_1851_);
v_i_1848_ = v___x_1855_;
v_bs_1849_ = v___x_1856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_bs_1860_){
_start:
{
size_t v_sz_boxed_1861_; size_t v_i_boxed_1862_; lean_object* v_res_1863_; 
v_sz_boxed_1861_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1862_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_boxed_1861_, v_i_boxed_1862_, v_bs_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object* v_as_1864_, size_t v_i_1865_, size_t v_stop_1866_, lean_object* v_b_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_a_1871_; lean_object* v_a_1872_; uint8_t v___x_1876_; 
v___x_1876_ = lean_usize_dec_eq(v_i_1865_, v_stop_1866_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_array_uget_borrowed(v_as_1864_, v_i_1865_);
lean_inc(v___x_1877_);
v___x_1878_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v___x_1877_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v_a_1880_; lean_object* v___x_1881_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
v_a_1880_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1878_);
v___x_1881_ = l_Array_append___redArg(v_b_1867_, v_a_1879_);
lean_dec(v_a_1879_);
v_a_1871_ = v___x_1881_;
v_a_1872_ = v_a_1880_;
goto v___jp_1870_;
}
else
{
lean_dec_ref(v_b_1867_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1882_; lean_object* v_a_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1882_);
v_a_1883_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1878_);
v_a_1871_ = v_a_1882_;
v_a_1872_ = v_a_1883_;
goto v___jp_1870_;
}
else
{
return v___x_1878_;
}
}
}
else
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_b_1867_);
lean_ctor_set(v___x_1884_, 1, v___y_1869_);
return v___x_1884_;
}
v___jp_1870_:
{
size_t v___x_1873_; size_t v___x_1874_; 
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_add(v_i_1865_, v___x_1873_);
v_i_1865_ = v___x_1874_;
v_b_1867_ = v_a_1871_;
v___y_1869_ = v_a_1872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object* v_as_1885_, lean_object* v_i_1886_, lean_object* v_stop_1887_, lean_object* v_b_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
size_t v_i_boxed_1891_; size_t v_stop_boxed_1892_; lean_object* v_res_1893_; 
v_i_boxed_1891_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_stop_boxed_1892_ = lean_unbox_usize(v_stop_1887_);
lean_dec(v_stop_1887_);
v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_1885_, v_i_boxed_1891_, v_stop_boxed_1892_, v_b_1888_, v___y_1889_, v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v_as_1885_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t v_sz_1894_, size_t v_i_1895_, lean_object* v_bs_1896_){
_start:
{
uint8_t v___x_1897_; 
v___x_1897_ = lean_usize_dec_lt(v_i_1895_, v_sz_1894_);
if (v___x_1897_ == 0)
{
return v_bs_1896_;
}
else
{
lean_object* v_v_1898_; lean_object* v___x_1899_; lean_object* v_bs_x27_1900_; size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v_v_1898_ = lean_array_uget(v_bs_1896_, v_i_1895_);
v___x_1899_ = lean_unsigned_to_nat(0u);
v_bs_x27_1900_ = lean_array_uset(v_bs_1896_, v_i_1895_, v___x_1899_);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1895_, v___x_1901_);
v___x_1903_ = lean_array_uset(v_bs_x27_1900_, v_i_1895_, v_v_1898_);
v_i_1895_ = v___x_1902_;
v_bs_1896_ = v___x_1903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_bs_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_boxed_1908_, v_i_boxed_1909_, v_bs_1907_);
return v_res_1910_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6));
v___x_1920_ = l_String_toRawSubstring_x27(v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25));
v___x_1961_ = l_String_toRawSubstring_x27(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52));
v___x_2031_ = l_String_toRawSubstring_x27(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55));
v___x_2035_ = l_String_toRawSubstring_x27(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58));
v___x_2040_ = l_String_toRawSubstring_x27(v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73));
v___x_2072_ = lean_mk_syntax_ident(v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76));
v___x_2077_ = lean_mk_syntax_ident(v___x_2076_);
return v___x_2077_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79));
v___x_2082_ = lean_mk_syntax_ident(v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83));
v___x_2091_ = l_String_toRawSubstring_x27(v___x_2090_);
return v___x_2091_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91));
v___x_2111_ = l_String_toRawSubstring_x27(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2123_ = l_String_toRawSubstring_x27(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72));
v___x_2129_ = l_String_toRawSubstring_x27(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object* v_monad_2153_, lean_object* v_mkMonadAdapt_2154_, lean_object* v_logExceptionsDefault_2155_, lean_object* v_mkLogExceptionsTerm_2156_, lean_object* v_doc_x3f_2157_, lean_object* v_vis_x3f_2158_, lean_object* v_tk_2159_, lean_object* v_elabName_2160_, lean_object* v_type_2161_, lean_object* v_binders_2162_, lean_object* v_entries_x3f_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; size_t v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; size_t v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; size_t v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; size_t v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2419_; lean_object* v___y_2420_; size_t v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; size_t v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v_a_2479_; lean_object* v_a_2480_; lean_object* v___y_2583_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0));
v___x_2168_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0));
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0));
v___x_2595_ = lean_array_get_size(v_binders_2162_);
v___x_2596_ = lean_nat_dec_lt(v___x_2166_, v___x_2595_);
if (v___x_2596_ == 0)
{
v_a_2479_ = v___x_2167_;
v_a_2480_ = v_a_2165_;
goto v___jp_2478_;
}
else
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_le(v___x_2595_, v___x_2595_);
if (v___x_2597_ == 0)
{
if (v___x_2596_ == 0)
{
v_a_2479_ = v___x_2167_;
v_a_2480_ = v_a_2165_;
goto v___jp_2478_;
}
else
{
size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = lean_usize_of_nat(v___x_2595_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_2162_, v___x_2598_, v___x_2599_, v___x_2167_, v_a_2164_, v_a_2165_);
v___y_2583_ = v___x_2600_;
goto v___jp_2582_;
}
}
else
{
size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = lean_usize_of_nat(v___x_2595_);
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_2162_, v___x_2601_, v___x_2602_, v___x_2167_, v_a_2164_, v_a_2165_);
v___y_2583_ = v___x_2603_;
goto v___jp_2582_;
}
}
v___jp_2170_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; size_t v_sz_2225_; lean_object* v___x_2226_; size_t v_sz_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_inc_ref_n(v___y_2205_, 2);
v___x_2207_ = l_Array_append___redArg(v___y_2205_, v___y_2206_);
lean_dec_ref(v___y_2206_);
lean_inc_n(v___y_2200_, 18);
lean_inc_n(v___y_2198_, 77);
v___x_2208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2198_);
lean_ctor_set(v___x_2208_, 1, v___y_2200_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_inc_n(v___y_2178_, 22);
v___x_2209_ = l_Lean_Syntax_node7(v___y_2198_, v___y_2197_, v___y_2176_, v___y_2178_, v___x_2208_, v___y_2178_, v___y_2178_, v___y_2178_, v___y_2178_);
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1));
lean_inc_ref_n(v___y_2194_, 4);
v___x_2211_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2194_, v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2));
v___x_2213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___y_2198_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3));
v___x_2215_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2194_, v___x_2214_);
lean_inc_n(v___y_2175_, 2);
v___x_2216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___y_2175_);
lean_ctor_set(v___x_2216_, 1, v___y_2200_);
lean_ctor_set(v___x_2216_, 2, v___x_2167_);
v___x_2217_ = lean_unsigned_to_nat(2u);
v___x_2218_ = lean_mk_empty_array_with_capacity(v___x_2217_);
v___x_2219_ = lean_array_push(v___x_2218_, v_elabName_2160_);
v___x_2220_ = lean_array_push(v___x_2219_, v___x_2216_);
v___x_2221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___y_2175_);
lean_ctor_set(v___x_2221_, 1, v___x_2215_);
lean_ctor_set(v___x_2221_, 2, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4));
v___x_2223_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2194_, v___x_2222_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v___y_2174_, v___y_2193_, v_binders_2162_);
v_sz_2225_ = lean_array_size(v___x_2224_);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_2225_, v___y_2193_, v___x_2224_);
v_sz_2227_ = lean_array_size(v___x_2226_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_2227_, v___y_2193_, v___x_2226_);
v___x_2229_ = l_Array_append___redArg(v___y_2205_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3));
lean_inc_ref(v___y_2203_);
v___x_2231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___y_2198_);
lean_ctor_set(v___x_2231_, 1, v___y_2203_);
v___x_2232_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___y_2181_);
v___x_2233_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5));
v___x_2234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___y_2198_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7);
v___x_2236_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9));
lean_inc_n(v___y_2196_, 5);
lean_inc_n(v___y_2202_, 5);
v___x_2237_ = l_Lean_addMacroScope(v___y_2202_, v___x_2236_, v___y_2196_);
lean_inc_n(v___y_2179_, 5);
v___x_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set(v___x_2238_, 1, v___y_2179_);
v___x_2239_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10));
lean_inc_n(v___y_2188_, 8);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___y_2188_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2238_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2198_);
lean_ctor_set(v___x_2242_, 1, v___x_2235_);
lean_ctor_set(v___x_2242_, 2, v___x_2237_);
lean_ctor_set(v___x_2242_, 3, v___x_2241_);
lean_inc_ref_n(v___x_2234_, 4);
v___x_2243_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2200_, v___x_2234_, v___x_2242_);
lean_inc_ref(v___y_2187_);
v___x_2244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___y_2198_);
lean_ctor_set(v___x_2244_, 1, v___y_2187_);
lean_inc_ref_n(v___x_2244_, 3);
lean_inc_ref_n(v___x_2231_, 3);
v___x_2245_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2230_, v___x_2231_, v___x_2232_, v___x_2243_, v___y_2178_, v___x_2244_);
v___x_2246_ = lean_array_push(v___x_2229_, v___x_2245_);
v___x_2247_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___y_2183_);
lean_inc_n(v_type_2161_, 2);
v___x_2248_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2200_, v___x_2234_, v_type_2161_);
v___x_2249_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12));
lean_inc_ref(v___y_2185_);
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___y_2198_);
lean_ctor_set(v___x_2250_, 1, v___y_2185_);
v___x_2251_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14));
v___x_2252_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16));
v___x_2253_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___y_2198_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18));
v___x_2256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___y_2198_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
lean_inc_ref(v___x_2256_);
lean_inc_ref(v___x_2254_);
v___x_2257_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2252_, v___x_2254_, v___x_2256_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20));
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22));
v___x_2260_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2259_, v___y_2178_);
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24));
v___x_2262_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2261_, v___y_2178_);
v___x_2263_ = l_Lean_Syntax_node6(v___y_2198_, v___x_2258_, v___x_2254_, v___y_2178_, v___x_2260_, v___x_2262_, v___y_2178_, v___x_2256_);
v___x_2264_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2251_, v___x_2257_, v___x_2263_);
lean_inc_ref_n(v___x_2250_, 5);
v___x_2265_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2249_, v___x_2250_, v___x_2264_);
v___x_2266_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2265_);
v___x_2267_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2230_, v___x_2231_, v___x_2247_, v___x_2248_, v___x_2266_, v___x_2244_);
v___x_2268_ = lean_array_push(v___x_2246_, v___x_2267_);
v___x_2269_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___y_2172_);
v___x_2270_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26);
v___x_2271_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27));
v___x_2272_ = l_Lean_addMacroScope(v___y_2202_, v___x_2271_, v___y_2196_);
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___y_2179_);
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28));
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___y_2188_);
v___x_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2198_);
lean_ctor_set(v___x_2277_, 1, v___x_2270_);
lean_ctor_set(v___x_2277_, 2, v___x_2272_);
lean_ctor_set(v___x_2277_, 3, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2200_, v___x_2234_, v___x_2277_);
v___x_2279_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2249_, v___x_2250_, v_logExceptionsDefault_2155_);
v___x_2280_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2279_);
v___x_2281_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2230_, v___x_2231_, v___x_2269_, v___x_2278_, v___x_2280_, v___x_2244_);
v___x_2282_ = lean_array_push(v___x_2268_, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2283_, 0, v___y_2198_);
lean_ctor_set(v___x_2283_, 1, v___y_2200_);
lean_ctor_set(v___x_2283_, 2, v___x_2282_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30));
v___x_2285_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v_type_2161_);
lean_inc(v___x_2285_);
lean_inc_n(v___y_2186_, 4);
v___x_2286_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2186_, v_monad_2153_, v___x_2285_);
v___x_2287_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2284_, v___x_2234_, v___x_2286_);
v___x_2288_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2223_, v___x_2283_, v___x_2288_);
v___x_2290_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31));
v___x_2291_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2194_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32));
v___x_2293_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33));
v___x_2294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___y_2198_);
lean_ctor_set(v___x_2294_, 1, v___x_2292_);
v___x_2295_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35));
v___x_2296_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37));
v___x_2297_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39));
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40));
v___x_2299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2198_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42));
v___x_2301_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2300_, v___y_2178_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44));
v___x_2303_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46));
v___x_2304_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48));
lean_inc_ref(v___y_2189_);
v___x_2305_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2305_, 0, v___y_2198_);
lean_ctor_set(v___x_2305_, 1, v___y_2189_);
lean_ctor_set(v___x_2305_, 2, v___y_2195_);
lean_ctor_set(v___x_2305_, 3, v___y_2188_);
v___x_2306_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2304_, v___x_2305_);
lean_inc_ref_n(v___y_2182_, 5);
v___x_2307_ = l_String_toRawSubstring_x27(v___y_2182_);
v___x_2308_ = l_Lean_Name_mkStr1(v___y_2182_);
v___x_2309_ = l_Lean_addMacroScope(v___y_2202_, v___x_2308_, v___y_2196_);
lean_inc_ref_n(v___y_2204_, 2);
lean_inc_ref_n(v___y_2171_, 2);
v___x_2310_ = l_Lean_Name_mkStr4(v___x_2168_, v___y_2171_, v___y_2204_, v___y_2182_);
lean_inc(v___x_2310_);
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___y_2179_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___y_2188_);
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2311_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2315_, 0, v___y_2198_);
lean_ctor_set(v___x_2315_, 1, v___x_2307_);
lean_ctor_set(v___x_2315_, 2, v___x_2309_);
lean_ctor_set(v___x_2315_, 3, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2186_, v___x_2315_, v___x_2285_);
v___x_2317_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2284_, v___x_2234_, v___x_2316_);
v___x_2318_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2317_);
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50));
v___x_2320_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51));
v___x_2321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___y_2198_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2319_, v___x_2321_, v___y_2184_);
v___x_2323_ = l_Array_append___redArg(v___y_2205_, v___y_2177_);
lean_dec_ref(v___y_2177_);
v___x_2324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2324_, 0, v___y_2198_);
lean_ctor_set(v___x_2324_, 1, v___y_2200_);
lean_ctor_set(v___x_2324_, 2, v___x_2323_);
v___x_2325_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2186_, v___x_2322_, v___x_2324_);
v___x_2326_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2303_, v___x_2306_, v___y_2178_, v___x_2318_, v___x_2250_, v___x_2325_);
v___x_2327_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2302_, v___x_2326_);
lean_inc(v___x_2301_);
lean_inc_ref(v___x_2299_);
v___x_2328_ = l_Lean_Syntax_node4(v___y_2198_, v___x_2297_, v___x_2299_, v___y_2178_, v___x_2301_, v___x_2327_);
v___x_2329_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2296_, v___x_2328_, v___y_2178_);
lean_inc_ref(v___y_2190_);
v___x_2330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2330_, 0, v___y_2198_);
lean_ctor_set(v___x_2330_, 1, v___y_2190_);
lean_ctor_set(v___x_2330_, 2, v___y_2180_);
lean_ctor_set(v___x_2330_, 3, v___y_2188_);
v___x_2331_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2304_, v___x_2330_);
v___x_2332_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54));
v___x_2334_ = l_Lean_Name_mkStr2(v___y_2182_, v___x_2333_);
v___x_2335_ = l_Lean_addMacroScope(v___y_2202_, v___x_2334_, v___y_2196_);
v___x_2336_ = l_Lean_Name_mkStr5(v___x_2168_, v___y_2171_, v___y_2204_, v___y_2182_, v___x_2333_);
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___y_2179_);
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___y_2188_);
v___x_2339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2339_, 0, v___y_2198_);
lean_ctor_set(v___x_2339_, 1, v___x_2332_);
lean_ctor_set(v___x_2339_, 2, v___x_2335_);
lean_ctor_set(v___x_2339_, 3, v___x_2338_);
v___x_2340_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56);
v___x_2341_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57));
v___x_2342_ = l_Lean_addMacroScope(v___y_2202_, v___x_2341_, v___y_2196_);
v___x_2343_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2343_, 0, v___y_2198_);
lean_ctor_set(v___x_2343_, 1, v___x_2340_);
lean_ctor_set(v___x_2343_, 2, v___x_2342_);
lean_ctor_set(v___x_2343_, 3, v___y_2188_);
v___x_2344_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59);
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60));
v___x_2346_ = l_Lean_addMacroScope(v___y_2202_, v___x_2345_, v___y_2196_);
v___x_2347_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61));
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___y_2179_);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___y_2188_);
v___x_2350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2198_);
lean_ctor_set(v___x_2350_, 1, v___x_2344_);
lean_ctor_set(v___x_2350_, 2, v___x_2346_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63));
v___x_2352_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64));
v___x_2353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___y_2198_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
lean_inc_ref(v___x_2353_);
v___x_2354_ = l_Lean_Syntax_node3(v___y_2198_, v___x_2351_, v___x_2353_, v___x_2353_, v_type_2161_);
v___x_2355_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2354_);
v___x_2356_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2186_, v___x_2350_, v___x_2355_);
v___x_2357_ = l_Lean_Syntax_node5(v___y_2198_, v___y_2201_, v___x_2231_, v___x_2343_, v___x_2250_, v___x_2356_, v___x_2244_);
v___x_2358_ = l_Lean_Syntax_node1(v___y_2198_, v___y_2200_, v___x_2357_);
v___x_2359_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2186_, v___x_2339_, v___x_2358_);
v___x_2360_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2303_, v___x_2331_, v___y_2178_, v___y_2178_, v___x_2250_, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2302_, v___x_2360_);
v___x_2362_ = l_Lean_Syntax_node4(v___y_2198_, v___x_2297_, v___x_2299_, v___y_2178_, v___x_2301_, v___x_2361_);
v___x_2363_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2296_, v___x_2362_, v___y_2178_);
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2365_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2364_, v___y_2191_);
v___x_2366_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2296_, v___x_2365_, v___y_2178_);
v___x_2367_ = l_Lean_Syntax_node3(v___y_2198_, v___y_2200_, v___x_2329_, v___x_2363_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v___y_2198_, v___x_2295_, v___x_2367_);
v___x_2369_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2293_, v___x_2294_, v___x_2368_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69));
v___x_2371_ = l_Lean_Syntax_node2(v___y_2198_, v___x_2370_, v___y_2178_, v___y_2178_);
v___x_2372_ = l_Lean_Syntax_node4(v___y_2198_, v___x_2291_, v___x_2250_, v___x_2369_, v___x_2371_, v___y_2178_);
v___x_2373_ = l_Lean_Syntax_node5(v___y_2198_, v___x_2211_, v___x_2213_, v___x_2221_, v___x_2289_, v___x_2372_, v___y_2178_);
v___x_2374_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2192_, v___x_2209_, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node2(v___y_2198_, v___y_2200_, v___y_2173_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___y_2199_);
return v___x_2376_;
}
v___jp_2377_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_inc_ref(v___y_2411_);
v___x_2413_ = l_Array_append___redArg(v___y_2411_, v___y_2412_);
lean_dec_ref(v___y_2412_);
lean_inc(v___y_2406_);
lean_inc(v___y_2404_);
v___x_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2404_);
lean_ctor_set(v___x_2414_, 1, v___y_2406_);
lean_ctor_set(v___x_2414_, 2, v___x_2413_);
if (lean_obj_tag(v_vis_x3f_2158_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2416_; 
v_val_2415_ = lean_ctor_get(v_vis_x3f_2158_, 0);
lean_inc(v_val_2415_);
lean_dec_ref(v_vis_x3f_2158_);
v___x_2416_ = l_Array_mkArray1___redArg(v_val_2415_);
v___y_2171_ = v___y_2378_;
v___y_2172_ = v___y_2379_;
v___y_2173_ = v___y_2380_;
v___y_2174_ = v___y_2381_;
v___y_2175_ = v___y_2382_;
v___y_2176_ = v___x_2414_;
v___y_2177_ = v___y_2383_;
v___y_2178_ = v___y_2384_;
v___y_2179_ = v___y_2385_;
v___y_2180_ = v___y_2387_;
v___y_2181_ = v___y_2386_;
v___y_2182_ = v___y_2388_;
v___y_2183_ = v___y_2389_;
v___y_2184_ = v___y_2390_;
v___y_2185_ = v___y_2391_;
v___y_2186_ = v___y_2392_;
v___y_2187_ = v___y_2393_;
v___y_2188_ = v___y_2394_;
v___y_2189_ = v___y_2395_;
v___y_2190_ = v___y_2396_;
v___y_2191_ = v___y_2397_;
v___y_2192_ = v___y_2398_;
v___y_2193_ = v___y_2399_;
v___y_2194_ = v___y_2400_;
v___y_2195_ = v___y_2401_;
v___y_2196_ = v___y_2402_;
v___y_2197_ = v___y_2403_;
v___y_2198_ = v___y_2404_;
v___y_2199_ = v___y_2405_;
v___y_2200_ = v___y_2406_;
v___y_2201_ = v___y_2409_;
v___y_2202_ = v___y_2408_;
v___y_2203_ = v___y_2407_;
v___y_2204_ = v___y_2410_;
v___y_2205_ = v___y_2411_;
v___y_2206_ = v___x_2416_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2417_; 
lean_dec(v_vis_x3f_2158_);
v___x_2417_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
v___y_2171_ = v___y_2378_;
v___y_2172_ = v___y_2379_;
v___y_2173_ = v___y_2380_;
v___y_2174_ = v___y_2381_;
v___y_2175_ = v___y_2382_;
v___y_2176_ = v___x_2414_;
v___y_2177_ = v___y_2383_;
v___y_2178_ = v___y_2384_;
v___y_2179_ = v___y_2385_;
v___y_2180_ = v___y_2387_;
v___y_2181_ = v___y_2386_;
v___y_2182_ = v___y_2388_;
v___y_2183_ = v___y_2389_;
v___y_2184_ = v___y_2390_;
v___y_2185_ = v___y_2391_;
v___y_2186_ = v___y_2392_;
v___y_2187_ = v___y_2393_;
v___y_2188_ = v___y_2394_;
v___y_2189_ = v___y_2395_;
v___y_2190_ = v___y_2396_;
v___y_2191_ = v___y_2397_;
v___y_2192_ = v___y_2398_;
v___y_2193_ = v___y_2399_;
v___y_2194_ = v___y_2400_;
v___y_2195_ = v___y_2401_;
v___y_2196_ = v___y_2402_;
v___y_2197_ = v___y_2403_;
v___y_2198_ = v___y_2404_;
v___y_2199_ = v___y_2405_;
v___y_2200_ = v___y_2406_;
v___y_2201_ = v___y_2409_;
v___y_2202_ = v___y_2408_;
v___y_2203_ = v___y_2407_;
v___y_2204_ = v___y_2410_;
v___y_2205_ = v___y_2411_;
v___y_2206_ = v___x_2417_;
goto v___jp_2170_;
}
}
v___jp_2418_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc_ref(v___y_2454_);
v___x_2457_ = l_Array_append___redArg(v___y_2454_, v___y_2456_);
lean_dec_ref(v___y_2456_);
lean_inc(v___y_2449_);
lean_inc_n(v___y_2447_, 2);
v___x_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___y_2447_);
lean_ctor_set(v___x_2458_, 1, v___y_2449_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
v___x_2459_ = lean_unsigned_to_nat(9u);
v___x_2460_ = lean_mk_empty_array_with_capacity(v___x_2459_);
lean_inc(v___y_2424_);
v___x_2461_ = lean_array_push(v___x_2460_, v___y_2424_);
v___x_2462_ = lean_array_push(v___x_2461_, v___y_2425_);
v___x_2463_ = lean_array_push(v___x_2462_, v___y_2455_);
v___x_2464_ = lean_array_push(v___x_2463_, v___y_2442_);
lean_inc(v___y_2433_);
v___x_2465_ = lean_array_push(v___x_2464_, v___y_2433_);
v___x_2466_ = lean_array_push(v___x_2465_, v___y_2431_);
v___x_2467_ = lean_array_push(v___x_2466_, v___y_2432_);
lean_inc(v_type_2161_);
v___x_2468_ = lean_array_push(v___x_2467_, v_type_2161_);
v___x_2469_ = lean_array_push(v___x_2468_, v___x_2458_);
lean_inc(v___y_2439_);
v___x_2470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2470_, 0, v___y_2447_);
lean_ctor_set(v___x_2470_, 1, v___y_2439_);
lean_ctor_set(v___x_2470_, 2, v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70));
lean_inc_ref_n(v___y_2444_, 2);
v___x_2472_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2444_, v___x_2471_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71));
v___x_2474_ = l_Lean_Name_mkStr4(v___x_2168_, v___x_2169_, v___y_2444_, v___x_2473_);
if (lean_obj_tag(v_doc_x3f_2157_) == 1)
{
lean_object* v_val_2475_; lean_object* v___x_2476_; 
v_val_2475_ = lean_ctor_get(v_doc_x3f_2157_, 0);
lean_inc(v_val_2475_);
lean_dec_ref(v_doc_x3f_2157_);
v___x_2476_ = l_Array_mkArray1___redArg(v_val_2475_);
v___y_2378_ = v___y_2419_;
v___y_2379_ = v___y_2420_;
v___y_2380_ = v___x_2470_;
v___y_2381_ = v___y_2421_;
v___y_2382_ = v___y_2422_;
v___y_2383_ = v___y_2423_;
v___y_2384_ = v___y_2424_;
v___y_2385_ = v___y_2426_;
v___y_2386_ = v___y_2427_;
v___y_2387_ = v___y_2428_;
v___y_2388_ = v___y_2429_;
v___y_2389_ = v___y_2430_;
v___y_2390_ = v___y_2433_;
v___y_2391_ = v___y_2434_;
v___y_2392_ = v___y_2435_;
v___y_2393_ = v___y_2436_;
v___y_2394_ = v___y_2437_;
v___y_2395_ = v___y_2438_;
v___y_2396_ = v___y_2440_;
v___y_2397_ = v___y_2441_;
v___y_2398_ = v___x_2472_;
v___y_2399_ = v___y_2443_;
v___y_2400_ = v___y_2444_;
v___y_2401_ = v___y_2445_;
v___y_2402_ = v___y_2446_;
v___y_2403_ = v___x_2474_;
v___y_2404_ = v___y_2447_;
v___y_2405_ = v___y_2448_;
v___y_2406_ = v___y_2449_;
v___y_2407_ = v___y_2452_;
v___y_2408_ = v___y_2451_;
v___y_2409_ = v___y_2450_;
v___y_2410_ = v___y_2453_;
v___y_2411_ = v___y_2454_;
v___y_2412_ = v___x_2476_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2477_; 
lean_dec(v_doc_x3f_2157_);
v___x_2477_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
v___y_2378_ = v___y_2419_;
v___y_2379_ = v___y_2420_;
v___y_2380_ = v___x_2470_;
v___y_2381_ = v___y_2421_;
v___y_2382_ = v___y_2422_;
v___y_2383_ = v___y_2423_;
v___y_2384_ = v___y_2424_;
v___y_2385_ = v___y_2426_;
v___y_2386_ = v___y_2427_;
v___y_2387_ = v___y_2428_;
v___y_2388_ = v___y_2429_;
v___y_2389_ = v___y_2430_;
v___y_2390_ = v___y_2433_;
v___y_2391_ = v___y_2434_;
v___y_2392_ = v___y_2435_;
v___y_2393_ = v___y_2436_;
v___y_2394_ = v___y_2437_;
v___y_2395_ = v___y_2438_;
v___y_2396_ = v___y_2440_;
v___y_2397_ = v___y_2441_;
v___y_2398_ = v___x_2472_;
v___y_2399_ = v___y_2443_;
v___y_2400_ = v___y_2444_;
v___y_2401_ = v___y_2445_;
v___y_2402_ = v___y_2446_;
v___y_2403_ = v___x_2474_;
v___y_2404_ = v___y_2447_;
v___y_2405_ = v___y_2448_;
v___y_2406_ = v___y_2449_;
v___y_2407_ = v___y_2452_;
v___y_2408_ = v___y_2451_;
v___y_2409_ = v___y_2450_;
v___y_2410_ = v___y_2453_;
v___y_2411_ = v___y_2454_;
v___y_2412_ = v___x_2477_;
goto v___jp_2377_;
}
}
v___jp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73));
v___x_2482_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74);
lean_inc_ref(v_a_2164_);
v___x_2483_ = lean_apply_3(v_mkLogExceptionsTerm_2156_, v___x_2482_, v_a_2164_, v_a_2480_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2581_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_a_2485_ = lean_ctor_get(v___x_2483_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2487_ = v___x_2483_;
v_isShared_2488_ = v_isSharedCheck_2581_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2581_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_quotContext_2489_; lean_object* v_currMacroScope_2490_; lean_object* v_ref_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v_quotContext_2489_ = lean_ctor_get(v_a_2164_, 1);
v_currMacroScope_2490_ = lean_ctor_get(v_a_2164_, 2);
v_ref_2491_ = lean_ctor_get(v_a_2164_, 5);
v___x_2492_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77);
v___x_2493_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80);
v___x_2494_ = 0;
v___x_2495_ = l_Lean_SourceInfo_fromRef(v_ref_2491_, v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82));
v___x_2497_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84);
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85));
v___x_2499_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87));
lean_inc_n(v_currMacroScope_2490_, 2);
lean_inc_n(v_quotContext_2489_, 2);
v___x_2500_ = l_Lean_addMacroScope(v_quotContext_2489_, v___x_2499_, v_currMacroScope_2490_);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1));
v___x_2502_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__2));
v___x_2503_ = lean_box(0);
v___x_2504_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90));
lean_inc_n(v___x_2495_, 3);
v___x_2505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2495_);
lean_ctor_set(v___x_2505_, 1, v___x_2497_);
lean_ctor_set(v___x_2505_, 2, v___x_2500_);
lean_ctor_set(v___x_2505_, 3, v___x_2504_);
v___x_2506_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3));
v___x_2507_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92);
v___x_2508_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93));
v___x_2509_ = l_Lean_addMacroScope(v_quotContext_2489_, v___x_2508_, v_currMacroScope_2490_);
lean_inc(v___x_2509_);
v___x_2510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2495_);
lean_ctor_set(v___x_2510_, 1, v___x_2507_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
lean_ctor_set(v___x_2510_, 3, v___x_2503_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95));
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 2);
lean_ctor_set(v___x_2487_, 1, v___x_2512_);
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2514_ = v___x_2487_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2515_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98);
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99));
lean_inc_n(v_currMacroScope_2490_, 2);
lean_inc_n(v_quotContext_2489_, 2);
v___x_2517_ = l_Lean_addMacroScope(v_quotContext_2489_, v___x_2516_, v_currMacroScope_2490_);
lean_inc(v___x_2517_);
lean_inc_n(v___x_2495_, 7);
v___x_2518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2495_);
lean_ctor_set(v___x_2518_, 1, v___x_2515_);
lean_ctor_set(v___x_2518_, 2, v___x_2517_);
lean_ctor_set(v___x_2518_, 3, v___x_2503_);
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100));
v___x_2520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2495_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2495_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
lean_inc_ref(v___x_2522_);
lean_inc_ref(v___x_2520_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2514_);
v___x_2523_ = l_Lean_Syntax_node5(v___x_2495_, v___x_2511_, v___x_2514_, v___x_2518_, v___x_2520_, v___x_2518_, v___x_2522_);
v___x_2524_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102);
v___x_2525_ = l_Lean_addMacroScope(v_quotContext_2489_, v___x_2481_, v_currMacroScope_2490_);
v___x_2526_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2495_);
lean_ctor_set(v___x_2526_, 1, v___x_2524_);
lean_ctor_set(v___x_2526_, 2, v___x_2525_);
lean_ctor_set(v___x_2526_, 3, v___x_2503_);
v___x_2527_ = l_Lean_Syntax_node5(v___x_2495_, v___x_2511_, v___x_2514_, v___x_2526_, v___x_2520_, v_a_2484_, v___x_2522_);
v___x_2528_ = l_Lean_Syntax_node5(v___x_2495_, v___x_2506_, v___x_2510_, v___x_2493_, v___x_2492_, v___x_2523_, v___x_2527_);
v___x_2529_ = l_Lean_Syntax_node2(v___x_2495_, v___x_2496_, v___x_2505_, v___x_2528_);
lean_inc_ref(v_a_2164_);
v___x_2530_ = lean_apply_3(v_mkMonadAdapt_2154_, v___x_2529_, v_a_2164_, v_a_2485_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2579_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_a_2532_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2534_ = v___x_2530_;
v_isShared_2535_ = v_isSharedCheck_2579_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2579_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_fnName_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_ref_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2536_ = l_Lean_TSyntax_getId(v_elabName_2160_);
v___x_2537_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104));
v___x_2538_ = l_Lean_Name_append(v___x_2536_, v___x_2537_);
v_fnName_2539_ = l_Lean_mkIdentFrom(v_elabName_2160_, v___x_2538_, v___x_2494_);
v___x_2540_ = lean_unsigned_to_nat(3u);
v___x_2541_ = lean_mk_empty_array_with_capacity(v___x_2540_);
v___x_2542_ = lean_array_push(v___x_2541_, v_tk_2159_);
lean_inc(v_elabName_2160_);
v___x_2543_ = lean_array_push(v___x_2542_, v_elabName_2160_);
lean_inc(v_type_2161_);
v___x_2544_ = lean_array_push(v___x_2543_, v_type_2161_);
v___x_2545_ = lean_box(2);
v___x_2546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2506_);
lean_ctor_set(v___x_2546_, 2, v___x_2544_);
v_ref_2547_ = l_Lean_replaceRef(v___x_2546_, v_ref_2491_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l_Lean_SourceInfo_fromRef(v_ref_2547_, v___x_2494_);
lean_dec(v_ref_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1));
v___x_2550_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__4);
lean_inc_n(v___x_2548_, 2);
v___x_2551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2548_);
lean_ctor_set(v___x_2551_, 1, v___x_2506_);
lean_ctor_set(v___x_2551_, 2, v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106));
v___x_2554_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107));
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 2);
lean_ctor_set(v___x_2534_, 1, v___x_2553_);
lean_ctor_set(v___x_2534_, 0, v___x_2548_);
v___x_2556_ = v___x_2534_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2553_);
v___x_2556_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_inc_n(v___x_2548_, 9);
v___x_2557_ = l_Lean_Syntax_node1(v___x_2548_, v___x_2554_, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node1(v___x_2548_, v___x_2506_, v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108));
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109));
v___x_2561_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110));
v___x_2562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2548_);
lean_ctor_set(v___x_2562_, 1, v___x_2560_);
v___x_2563_ = l_Lean_Syntax_node1(v___x_2548_, v___x_2561_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node1(v___x_2548_, v___x_2506_, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node1(v___x_2548_, v___x_2559_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111));
v___x_2567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2548_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v_sz_2568_ = lean_array_size(v_binders_2162_);
v___x_2569_ = ((size_t)0ULL);
lean_inc_ref(v_binders_2162_);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_2568_, v___x_2569_, v_binders_2162_);
v___x_2571_ = l_Array_append___redArg(v___x_2550_, v___x_2570_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2548_);
lean_ctor_set(v___x_2572_, 1, v___x_2506_);
lean_ctor_set(v___x_2572_, 2, v___x_2571_);
v___x_2573_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__112));
v___x_2574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2548_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
if (lean_obj_tag(v_entries_x3f_2163_) == 1)
{
lean_object* v_val_2575_; lean_object* v___x_2576_; 
v_val_2575_ = lean_ctor_get(v_entries_x3f_2163_, 0);
lean_inc(v_val_2575_);
lean_dec_ref(v_entries_x3f_2163_);
v___x_2576_ = l_Array_mkArray1___redArg(v_val_2575_);
lean_inc(v_quotContext_2489_);
lean_inc(v_currMacroScope_2490_);
v___y_2419_ = v___x_2501_;
v___y_2420_ = v___x_2482_;
v___y_2421_ = v_sz_2568_;
v___y_2422_ = v___x_2545_;
v___y_2423_ = v_a_2479_;
v___y_2424_ = v___x_2551_;
v___y_2425_ = v___x_2558_;
v___y_2426_ = v___x_2503_;
v___y_2427_ = v___x_2492_;
v___y_2428_ = v___x_2517_;
v___y_2429_ = v___x_2498_;
v___y_2430_ = v___x_2493_;
v___y_2431_ = v___x_2572_;
v___y_2432_ = v___x_2574_;
v___y_2433_ = v_fnName_2539_;
v___y_2434_ = v___x_2519_;
v___y_2435_ = v___x_2496_;
v___y_2436_ = v___x_2521_;
v___y_2437_ = v___x_2503_;
v___y_2438_ = v___x_2507_;
v___y_2439_ = v___x_2549_;
v___y_2440_ = v___x_2515_;
v___y_2441_ = v_a_2531_;
v___y_2442_ = v___x_2567_;
v___y_2443_ = v___x_2569_;
v___y_2444_ = v___x_2552_;
v___y_2445_ = v___x_2509_;
v___y_2446_ = v_currMacroScope_2490_;
v___y_2447_ = v___x_2548_;
v___y_2448_ = v_a_2532_;
v___y_2449_ = v___x_2506_;
v___y_2450_ = v___x_2511_;
v___y_2451_ = v_quotContext_2489_;
v___y_2452_ = v___x_2512_;
v___y_2453_ = v___x_2502_;
v___y_2454_ = v___x_2550_;
v___y_2455_ = v___x_2565_;
v___y_2456_ = v___x_2576_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2577_; 
lean_dec(v_entries_x3f_2163_);
v___x_2577_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__5));
lean_inc(v_quotContext_2489_);
lean_inc(v_currMacroScope_2490_);
v___y_2419_ = v___x_2501_;
v___y_2420_ = v___x_2482_;
v___y_2421_ = v_sz_2568_;
v___y_2422_ = v___x_2545_;
v___y_2423_ = v_a_2479_;
v___y_2424_ = v___x_2551_;
v___y_2425_ = v___x_2558_;
v___y_2426_ = v___x_2503_;
v___y_2427_ = v___x_2492_;
v___y_2428_ = v___x_2517_;
v___y_2429_ = v___x_2498_;
v___y_2430_ = v___x_2493_;
v___y_2431_ = v___x_2572_;
v___y_2432_ = v___x_2574_;
v___y_2433_ = v_fnName_2539_;
v___y_2434_ = v___x_2519_;
v___y_2435_ = v___x_2496_;
v___y_2436_ = v___x_2521_;
v___y_2437_ = v___x_2503_;
v___y_2438_ = v___x_2507_;
v___y_2439_ = v___x_2549_;
v___y_2440_ = v___x_2515_;
v___y_2441_ = v_a_2531_;
v___y_2442_ = v___x_2567_;
v___y_2443_ = v___x_2569_;
v___y_2444_ = v___x_2552_;
v___y_2445_ = v___x_2509_;
v___y_2446_ = v_currMacroScope_2490_;
v___y_2447_ = v___x_2548_;
v___y_2448_ = v_a_2532_;
v___y_2449_ = v___x_2506_;
v___y_2450_ = v___x_2511_;
v___y_2451_ = v_quotContext_2489_;
v___y_2452_ = v___x_2512_;
v___y_2453_ = v___x_2502_;
v___y_2454_ = v___x_2550_;
v___y_2455_ = v___x_2565_;
v___y_2456_ = v___x_2577_;
goto v___jp_2418_;
}
}
}
}
else
{
lean_dec(v___x_2517_);
lean_dec(v___x_2509_);
lean_dec_ref(v_a_2479_);
lean_dec(v_entries_x3f_2163_);
lean_dec_ref(v_binders_2162_);
lean_dec(v_type_2161_);
lean_dec(v_elabName_2160_);
lean_dec(v_tk_2159_);
lean_dec(v_vis_x3f_2158_);
lean_dec(v_doc_x3f_2157_);
lean_dec(v_logExceptionsDefault_2155_);
lean_dec(v_monad_2153_);
return v___x_2530_;
}
}
}
}
else
{
lean_dec_ref(v_a_2479_);
lean_dec(v_entries_x3f_2163_);
lean_dec_ref(v_binders_2162_);
lean_dec(v_type_2161_);
lean_dec(v_elabName_2160_);
lean_dec(v_tk_2159_);
lean_dec(v_vis_x3f_2158_);
lean_dec(v_doc_x3f_2157_);
lean_dec(v_logExceptionsDefault_2155_);
lean_dec_ref(v_mkMonadAdapt_2154_);
lean_dec(v_monad_2153_);
return v___x_2483_;
}
}
v___jp_2582_:
{
if (lean_obj_tag(v___y_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v_a_2585_; 
v_a_2584_ = lean_ctor_get(v___y_2583_, 0);
lean_inc(v_a_2584_);
v_a_2585_ = lean_ctor_get(v___y_2583_, 1);
lean_inc(v_a_2585_);
lean_dec_ref(v___y_2583_);
v_a_2479_ = v_a_2584_;
v_a_2480_ = v_a_2585_;
goto v___jp_2478_;
}
else
{
lean_object* v_a_2586_; lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_entries_x3f_2163_);
lean_dec_ref(v_binders_2162_);
lean_dec(v_type_2161_);
lean_dec(v_elabName_2160_);
lean_dec(v_tk_2159_);
lean_dec(v_vis_x3f_2158_);
lean_dec(v_doc_x3f_2157_);
lean_dec_ref(v_mkLogExceptionsTerm_2156_);
lean_dec(v_logExceptionsDefault_2155_);
lean_dec_ref(v_mkMonadAdapt_2154_);
lean_dec(v_monad_2153_);
v_a_2586_ = lean_ctor_get(v___y_2583_, 0);
v_a_2587_ = lean_ctor_get(v___y_2583_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___y_2583_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___y_2583_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_inc(v_a_2586_);
lean_dec(v___y_2583_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2586_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object* v_monad_2604_, lean_object* v_mkMonadAdapt_2605_, lean_object* v_logExceptionsDefault_2606_, lean_object* v_mkLogExceptionsTerm_2607_, lean_object* v_doc_x3f_2608_, lean_object* v_vis_x3f_2609_, lean_object* v_tk_2610_, lean_object* v_elabName_2611_, lean_object* v_type_2612_, lean_object* v_binders_2613_, lean_object* v_entries_x3f_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v_monad_2604_, v_mkMonadAdapt_2605_, v_logExceptionsDefault_2606_, v_mkLogExceptionsTerm_2607_, v_doc_x3f_2608_, v_vis_x3f_2609_, v_tk_2610_, v_elabName_2611_, v_type_2612_, v_binders_2613_, v_entries_x3f_2614_, v_a_2615_, v_a_2616_);
lean_dec_ref(v_a_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0(lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2652_);
lean_ctor_set(v___x_2655_, 1, v___y_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0___boxed(lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__0(v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1(lean_object* v_logExceptions_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_logExceptions_2660_);
lean_ctor_set(v___x_2663_, 1, v___y_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1___boxed(lean_object* v_logExceptions_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___lam__1(v_logExceptions_2664_, v___y_2665_, v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2667_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__4));
v___x_2677_ = l_Lean_mkCIdent(v___x_2676_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__7));
v___x_2683_ = l_Lean_mkCIdent(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1(lean_object* v_x_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
lean_inc(v_x_2684_);
v___x_2688_ = l_Lean_Syntax_isOfKind(v_x_2684_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v_x_2684_);
v___x_2689_ = lean_box(1);
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_a_2686_);
return v___x_2690_;
}
else
{
lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v_tk_2698_; lean_object* v___x_2699_; lean_object* v_elabName_2700_; lean_object* v___x_2701_; lean_object* v_type_2702_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___y_2746_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___f_2691_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0));
v___f_2692_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__1));
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2693_);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(2u);
v_tk_2698_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2697_);
v___x_2699_ = lean_unsigned_to_nat(3u);
v_elabName_2700_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(4u);
v_type_2702_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2701_);
v___x_2743_ = lean_unsigned_to_nat(5u);
v___x_2744_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2743_);
v___x_2758_ = lean_unsigned_to_nat(6u);
v___x_2759_ = l_Lean_Syntax_getArg(v_x_2684_, v___x_2758_);
lean_dec(v_x_2684_);
v___x_2760_ = l_Lean_Syntax_getOptional_x3f(v___x_2759_);
lean_dec(v___x_2759_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_box(0);
v___y_2746_ = v___x_2761_;
goto v___jp_2745_;
}
else
{
lean_object* v_val_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_val_2762_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2760_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_val_2762_);
lean_dec(v___x_2760_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_val_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
v___y_2746_ = v___x_2767_;
goto v___jp_2745_;
}
}
}
v___jp_2703_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__5);
v___x_2709_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__8);
v___x_2710_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2708_, v___f_2691_, v___x_2709_, v___f_2692_, v___y_2707_, v___y_2705_, v_tk_2698_, v_elabName_2700_, v_type_2702_, v___y_2704_, v___y_2706_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_a_2712_ = lean_ctor_get(v___x_2710_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2710_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2711_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_a_2720_ = lean_ctor_get(v___x_2710_, 0);
v_a_2721_ = lean_ctor_get(v___x_2710_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2710_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_inc(v_a_2720_);
lean_dec(v___x_2710_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
v___jp_2729_:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Syntax_getOptional_x3f(v___x_2694_);
lean_dec(v___x_2694_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_box(0);
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___y_2732_;
v___y_2706_ = v___y_2731_;
v___y_2707_ = v___x_2734_;
goto v___jp_2703_;
}
else
{
lean_object* v_val_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_val_2735_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_val_2735_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_val_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___y_2732_;
v___y_2706_ = v___y_2731_;
v___y_2707_ = v___x_2740_;
goto v___jp_2703_;
}
}
}
}
v___jp_2745_:
{
lean_object* v_binders_2747_; lean_object* v___x_2748_; 
v_binders_2747_ = l_Lean_Syntax_getArgs(v___x_2744_);
lean_dec(v___x_2744_);
v___x_2748_ = l_Lean_Syntax_getOptional_x3f(v___x_2696_);
lean_dec(v___x_2696_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_box(0);
v___y_2730_ = v_binders_2747_;
v___y_2731_ = v___y_2746_;
v___y_2732_ = v___x_2749_;
goto v___jp_2729_;
}
else
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
v_val_2750_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v___x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
v___y_2730_ = v_binders_2747_;
v___y_2731_ = v___y_2746_;
v___y_2732_ = v___x_2755_;
goto v___jp_2729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___boxed(lean_object* v_x_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1(v_x_2770_, v_a_2771_, v_a_2772_);
lean_dec_ref(v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2779_ = lean_unsigned_to_nat(2u);
v___x_2780_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2778_, v___x_2779_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
return v_res_2785_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed), 4, 0);
v___x_2787_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_2790_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0);
v___x_2791_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2789_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object* v_a_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
return v_res_2793_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__8));
v___x_2840_ = l_String_toRawSubstring_x27(v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__13));
v___x_2846_ = l_String_toRawSubstring_x27(v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__20));
v___x_2861_ = l_String_toRawSubstring_x27(v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1(lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v_logExceptions_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_quotContext_2872_; lean_object* v_currMacroScope_2873_; lean_object* v_ref_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_quotContext_2872_ = lean_ctor_get(v___y_2870_, 1);
v_currMacroScope_2873_ = lean_ctor_get(v___y_2870_, 2);
v_ref_2874_ = lean_ctor_get(v___y_2870_, 5);
v___x_2875_ = 0;
v___x_2876_ = l_Lean_SourceInfo_fromRef(v_ref_2874_, v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__1));
v___x_2878_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__2));
lean_inc_n(v___x_2876_, 13);
v___x_2879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2876_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__3));
lean_inc_ref_n(v___x_2866_, 4);
lean_inc_ref_n(v___x_2865_, 3);
lean_inc_ref_n(v___x_2864_, 8);
v___x_2881_ = l_Lean_Name_mkStr4(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2880_);
v___x_2882_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__4));
v___x_2883_ = l_Lean_Name_mkStr4(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__5));
v___x_2885_ = l_Lean_Name_mkStr4(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
v___x_2887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2876_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__7));
v___x_2889_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9);
v___x_2890_ = lean_box(0);
lean_inc_n(v_currMacroScope_2873_, 3);
lean_inc_n(v_quotContext_2872_, 3);
v___x_2891_ = l_Lean_addMacroScope(v_quotContext_2872_, v___x_2890_, v_currMacroScope_2873_);
lean_inc_ref_n(v___x_2867_, 2);
v___x_2892_ = l_Lean_Name_mkStr3(v___x_2864_, v___x_2867_, v___x_2868_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__10));
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_2896_ = l_Lean_Name_mkStr3(v___x_2864_, v___x_2894_, v___x_2895_);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
v___x_2898_ = l_Lean_Name_mkStr3(v___x_2864_, v___x_2867_, v___x_2895_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = l_Lean_Name_mkStr3(v___x_2864_, v___x_2867_, v___x_2866_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
v___x_2902_ = l_Lean_Name_mkStr2(v___x_2864_, v___x_2894_);
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2901_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2899_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2897_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2893_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2876_);
lean_ctor_set(v___x_2910_, 1, v___x_2889_);
lean_ctor_set(v___x_2910_, 2, v___x_2891_);
lean_ctor_set(v___x_2910_, 3, v___x_2909_);
v___x_2911_ = l_Lean_Syntax_node1(v___x_2876_, v___x_2888_, v___x_2910_);
v___x_2912_ = l_Lean_Syntax_node2(v___x_2876_, v___x_2885_, v___x_2887_, v___x_2911_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__11));
v___x_2914_ = l_Lean_Name_mkStr4(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2913_);
v___x_2915_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__12));
v___x_2916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2876_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14);
v___x_2918_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__15));
v___x_2919_ = l_Lean_addMacroScope(v_quotContext_2872_, v___x_2918_, v_currMacroScope_2873_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__19));
v___x_2921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2876_);
lean_ctor_set(v___x_2921_, 1, v___x_2917_);
lean_ctor_set(v___x_2921_, 2, v___x_2919_);
lean_ctor_set(v___x_2921_, 3, v___x_2920_);
v___x_2922_ = l_Lean_Syntax_node2(v___x_2876_, v___x_2914_, v___x_2916_, v___x_2921_);
v___x_2923_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_2924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2876_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = l_Lean_Syntax_node3(v___x_2876_, v___x_2883_, v___x_2912_, v___x_2922_, v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5));
v___x_2927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2876_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__21);
v___x_2929_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__22));
v___x_2930_ = l_Lean_addMacroScope(v_quotContext_2872_, v___x_2929_, v_currMacroScope_2873_);
v___x_2931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2876_);
lean_ctor_set(v___x_2931_, 1, v___x_2928_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
lean_ctor_set(v___x_2931_, 3, v___x_2904_);
v___x_2932_ = l_Lean_Syntax_node3(v___x_2876_, v___x_2881_, v___x_2925_, v___x_2927_, v___x_2931_);
v___x_2933_ = l_Lean_Syntax_node3(v___x_2876_, v___x_2877_, v_logExceptions_2869_, v___x_2879_, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v___y_2871_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___boxed(lean_object* v___x_2935_, lean_object* v___x_2936_, lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v___x_2939_, lean_object* v_logExceptions_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1(v___x_2935_, v___x_2936_, v___x_2937_, v___x_2938_, v___x_2939_, v_logExceptions_2940_, v___y_2941_, v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2943_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__2));
v___x_2950_ = l_Lean_mkCIdent(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1(lean_object* v_x_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2960_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0));
v___x_2961_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1));
v___x_2962_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
lean_inc(v_x_2957_);
v___x_2963_ = l_Lean_Syntax_isOfKind(v_x_2957_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_x_2957_);
v___x_2964_ = lean_box(1);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_a_2959_);
return v___x_2965_;
}
else
{
lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v_tk_2972_; lean_object* v___x_2973_; lean_object* v_elabName_2974_; lean_object* v___x_2975_; lean_object* v_type_2976_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___y_3026_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___f_2966_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0));
v___x_2967_ = lean_unsigned_to_nat(0u);
v___x_2968_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_2967_);
v___x_2969_ = lean_unsigned_to_nat(1u);
v___x_2970_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_2969_);
v___x_2971_ = lean_unsigned_to_nat(2u);
v_tk_2972_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_2971_);
v___x_2973_ = lean_unsigned_to_nat(3u);
v_elabName_2974_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_2973_);
v___x_2975_ = lean_unsigned_to_nat(4u);
v_type_2976_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_2975_);
v___x_3023_ = lean_unsigned_to_nat(5u);
v___x_3024_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_3023_);
v___x_3040_ = lean_unsigned_to_nat(6u);
v___x_3041_ = l_Lean_Syntax_getArg(v_x_2957_, v___x_3040_);
lean_dec(v_x_2957_);
v___x_3042_ = l_Lean_Syntax_getOptional_x3f(v___x_3041_);
lean_dec(v___x_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_box(0);
v___y_3026_ = v___x_3043_;
goto v___jp_3025_;
}
else
{
lean_object* v_val_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_val_3044_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3042_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_val_3044_);
lean_dec(v___x_3042_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_val_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v___y_3026_ = v___x_3049_;
goto v___jp_3025_;
}
}
}
v___jp_2977_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2984_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__0));
lean_inc_ref(v___y_2982_);
v___x_2985_ = l_Lean_Name_mkStr4(v___x_2960_, v___x_2961_, v___y_2982_, v___x_2984_);
v___x_2986_ = l_Lean_mkCIdent(v___x_2985_);
v___x_2987_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3);
lean_inc_ref(v___y_2978_);
v___x_2988_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2986_, v___f_2966_, v___x_2987_, v___y_2978_, v___y_2983_, v___y_2980_, v_tk_2972_, v_elabName_2974_, v_type_2976_, v___y_2981_, v___y_2979_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_a_2990_ = lean_ctor_get(v___x_2988_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2988_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2989_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2998_ = lean_ctor_get(v___x_2988_, 0);
v_a_2999_ = lean_ctor_get(v___x_2988_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2988_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_inc(v_a_2998_);
lean_dec(v___x_2988_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2998_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
v___jp_3007_:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Syntax_getOptional_x3f(v___x_2968_);
lean_dec(v___x_2968_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_box(0);
v___y_2978_ = v___y_3010_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___y_3012_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___y_3009_;
v___y_2983_ = v___x_3014_;
goto v___jp_2977_;
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_val_3015_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_val_3015_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_val_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
v___y_2978_ = v___y_3010_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___y_3012_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___y_3009_;
v___y_2983_ = v___x_3020_;
goto v___jp_2977_;
}
}
}
}
v___jp_3025_:
{
lean_object* v___x_3027_; lean_object* v___f_3028_; lean_object* v_binders_3029_; lean_object* v___x_3030_; 
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
v___f_3028_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__4));
v_binders_3029_ = l_Lean_Syntax_getArgs(v___x_3024_);
lean_dec(v___x_3024_);
v___x_3030_ = l_Lean_Syntax_getOptional_x3f(v___x_2970_);
lean_dec(v___x_2970_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_box(0);
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___x_3027_;
v___y_3010_ = v___f_3028_;
v___y_3011_ = v_binders_3029_;
v___y_3012_ = v___x_3031_;
goto v___jp_3007_;
}
else
{
lean_object* v_val_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_val_3032_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3030_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_val_3032_);
lean_dec(v___x_3030_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_val_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___x_3027_;
v___y_3010_ = v___f_3028_;
v___y_3011_ = v_binders_3029_;
v___y_3012_ = v___x_3037_;
goto v___jp_3007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___boxed(lean_object* v_x_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1(v_x_3052_, v_a_3053_, v_a_3054_);
lean_dec_ref(v_a_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_3061_ = lean_unsigned_to_nat(2u);
v___x_3062_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_3060_, v___x_3061_, v_a_3056_, v_a_3057_, v_a_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
return v_res_3067_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed), 4, 0);
v___x_3069_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0);
v___x_3073_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3071_, v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
return v_res_3075_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__0));
v___x_3112_ = l_String_toRawSubstring_x27(v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1(lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v_logExceptions_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_quotContext_3123_; lean_object* v_currMacroScope_3124_; lean_object* v_ref_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_quotContext_3123_ = lean_ctor_get(v___y_3121_, 1);
v_currMacroScope_3124_ = lean_ctor_get(v___y_3121_, 2);
v_ref_3125_ = lean_ctor_get(v___y_3121_, 5);
v___x_3126_ = 0;
v___x_3127_ = l_Lean_SourceInfo_fromRef(v_ref_3125_, v___x_3126_);
v___x_3128_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__1));
v___x_3129_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__2));
lean_inc_n(v___x_3127_, 13);
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3127_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__3));
lean_inc_ref_n(v___x_3117_, 4);
lean_inc_ref_n(v___x_3116_, 3);
lean_inc_ref_n(v___x_3115_, 8);
v___x_3132_ = l_Lean_Name_mkStr4(v___x_3115_, v___x_3116_, v___x_3117_, v___x_3131_);
v___x_3133_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__4));
v___x_3134_ = l_Lean_Name_mkStr4(v___x_3115_, v___x_3116_, v___x_3117_, v___x_3133_);
v___x_3135_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__5));
v___x_3136_ = l_Lean_Name_mkStr4(v___x_3115_, v___x_3116_, v___x_3117_, v___x_3135_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3127_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__7));
v___x_3140_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__9);
v___x_3141_ = lean_box(0);
lean_inc_n(v_currMacroScope_3124_, 3);
lean_inc_n(v_quotContext_3123_, 3);
v___x_3142_ = l_Lean_addMacroScope(v_quotContext_3123_, v___x_3141_, v_currMacroScope_3124_);
lean_inc_ref_n(v___x_3118_, 2);
v___x_3143_ = l_Lean_Name_mkStr3(v___x_3115_, v___x_3118_, v___x_3119_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
v___x_3145_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__10));
v___x_3146_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_3147_ = l_Lean_Name_mkStr3(v___x_3115_, v___x_3145_, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
v___x_3149_ = l_Lean_Name_mkStr3(v___x_3115_, v___x_3118_, v___x_3146_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
v___x_3151_ = l_Lean_Name_mkStr3(v___x_3115_, v___x_3118_, v___x_3117_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
v___x_3153_ = l_Lean_Name_mkStr2(v___x_3115_, v___x_3145_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3152_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3150_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3148_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3144_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3127_);
lean_ctor_set(v___x_3161_, 1, v___x_3140_);
lean_ctor_set(v___x_3161_, 2, v___x_3142_);
lean_ctor_set(v___x_3161_, 3, v___x_3160_);
v___x_3162_ = l_Lean_Syntax_node1(v___x_3127_, v___x_3139_, v___x_3161_);
v___x_3163_ = l_Lean_Syntax_node2(v___x_3127_, v___x_3136_, v___x_3138_, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__11));
v___x_3165_ = l_Lean_Name_mkStr4(v___x_3115_, v___x_3116_, v___x_3117_, v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__12));
v___x_3167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3127_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__14);
v___x_3169_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__15));
v___x_3170_ = l_Lean_addMacroScope(v_quotContext_3123_, v___x_3169_, v_currMacroScope_3124_);
v___x_3171_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___lam__1___closed__19));
v___x_3172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3127_);
lean_ctor_set(v___x_3172_, 1, v___x_3168_);
lean_ctor_set(v___x_3172_, 2, v___x_3170_);
lean_ctor_set(v___x_3172_, 3, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node2(v___x_3127_, v___x_3165_, v___x_3167_, v___x_3172_);
v___x_3174_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_3175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3127_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_Syntax_node3(v___x_3127_, v___x_3134_, v___x_3163_, v___x_3173_, v___x_3175_);
v___x_3177_ = ((lean_object*)(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5));
v___x_3178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3127_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__1);
v___x_3180_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___closed__2));
v___x_3181_ = l_Lean_addMacroScope(v_quotContext_3123_, v___x_3180_, v_currMacroScope_3124_);
v___x_3182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3127_);
lean_ctor_set(v___x_3182_, 1, v___x_3179_);
lean_ctor_set(v___x_3182_, 2, v___x_3181_);
lean_ctor_set(v___x_3182_, 3, v___x_3155_);
v___x_3183_ = l_Lean_Syntax_node3(v___x_3127_, v___x_3132_, v___x_3176_, v___x_3178_, v___x_3182_);
v___x_3184_ = l_Lean_Syntax_node3(v___x_3127_, v___x_3128_, v_logExceptions_3120_, v___x_3130_, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v___y_3122_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1___boxed(lean_object* v___x_3186_, lean_object* v___x_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v___x_3190_, lean_object* v_logExceptions_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___lam__1(v___x_3186_, v___x_3187_, v___x_3188_, v___x_3189_, v___x_3190_, v_logExceptions_3191_, v___y_3192_, v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3194_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__2));
v___x_3203_ = l_Lean_mkCIdent(v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1(lean_object* v_x_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
lean_inc(v_x_3210_);
v___x_3214_ = l_Lean_Syntax_isOfKind(v_x_3210_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v_x_3210_);
v___x_3215_ = lean_box(1);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v_a_3212_);
return v___x_3216_;
}
else
{
lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v_tk_3223_; lean_object* v___x_3224_; lean_object* v_elabName_3225_; lean_object* v___x_3226_; lean_object* v_type_3227_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___y_3273_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___f_3217_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__0));
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3218_);
v___x_3220_ = lean_unsigned_to_nat(1u);
v___x_3221_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3220_);
v___x_3222_ = lean_unsigned_to_nat(2u);
v_tk_3223_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3222_);
v___x_3224_ = lean_unsigned_to_nat(3u);
v_elabName_3225_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3224_);
v___x_3226_ = lean_unsigned_to_nat(4u);
v_type_3227_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3226_);
v___x_3270_ = lean_unsigned_to_nat(5u);
v___x_3271_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3270_);
v___x_3286_ = lean_unsigned_to_nat(6u);
v___x_3287_ = l_Lean_Syntax_getArg(v_x_3210_, v___x_3286_);
lean_dec(v_x_3210_);
v___x_3288_ = l_Lean_Syntax_getOptional_x3f(v___x_3287_);
lean_dec(v___x_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_box(0);
v___y_3273_ = v___x_3289_;
goto v___jp_3272_;
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_val_3290_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3288_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_val_3290_);
lean_dec(v___x_3288_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_val_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
v___y_3273_ = v___x_3295_;
goto v___jp_3272_;
}
}
}
v___jp_3228_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__3);
v___x_3235_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3);
lean_inc_ref(v___y_3229_);
v___x_3236_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_3234_, v___f_3217_, v___x_3235_, v___y_3229_, v___y_3233_, v___y_3231_, v_tk_3223_, v_elabName_3225_, v_type_3227_, v___y_3230_, v___y_3232_, v_a_3211_, v_a_3212_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_a_3238_ = lean_ctor_get(v___x_3236_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3236_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3237_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
v_a_3246_ = lean_ctor_get(v___x_3236_, 0);
v_a_3247_ = lean_ctor_get(v___x_3236_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3236_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_inc(v_a_3246_);
lean_dec(v___x_3236_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3246_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
v___jp_3255_:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Syntax_getOptional_x3f(v___x_3219_);
lean_dec(v___x_3219_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_box(0);
v___y_3229_ = v___y_3256_;
v___y_3230_ = v___y_3258_;
v___y_3231_ = v___y_3259_;
v___y_3232_ = v___y_3257_;
v___y_3233_ = v___x_3261_;
goto v___jp_3228_;
}
else
{
lean_object* v_val_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
v_val_3262_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3260_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_val_3262_);
lean_dec(v___x_3260_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_val_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
v___y_3229_ = v___y_3256_;
v___y_3230_ = v___y_3258_;
v___y_3231_ = v___y_3259_;
v___y_3232_ = v___y_3257_;
v___y_3233_ = v___x_3267_;
goto v___jp_3228_;
}
}
}
}
v___jp_3272_:
{
lean_object* v___f_3274_; lean_object* v_binders_3275_; lean_object* v___x_3276_; 
v___f_3274_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___closed__4));
v_binders_3275_ = l_Lean_Syntax_getArgs(v___x_3271_);
lean_dec(v___x_3271_);
v___x_3276_ = l_Lean_Syntax_getOptional_x3f(v___x_3221_);
lean_dec(v___x_3221_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_box(0);
v___y_3256_ = v___f_3274_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v_binders_3275_;
v___y_3259_ = v___x_3277_;
goto v___jp_3255_;
}
else
{
lean_object* v_val_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
v_val_3278_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_val_3278_);
lean_dec(v___x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_val_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
v___y_3256_ = v___f_3274_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v_binders_3275_;
v___y_3259_ = v___x_3283_;
goto v___jp_3255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1___boxed(lean_object* v_x_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTacticConfig__1(v_x_3298_, v_a_3299_, v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_3307_ = lean_unsigned_to_nat(2u);
v___x_3308_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_3306_, v___x_3307_, v_a_3302_, v_a_3303_, v_a_3304_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(v_a_3309_, v_a_3310_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
return v_res_3313_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed), 4, 0);
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
v___x_3318_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0);
v___x_3319_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
return v_res_3321_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__0));
v___x_3358_ = l_String_toRawSubstring_x27(v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1(lean_object* v___x_3360_, lean_object* v___x_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v_eval_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_quotContext_3368_; lean_object* v_currMacroScope_3369_; lean_object* v_ref_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_quotContext_3368_ = lean_ctor_get(v___y_3366_, 1);
v_currMacroScope_3369_ = lean_ctor_get(v___y_3366_, 2);
v_ref_3370_ = lean_ctor_get(v___y_3366_, 5);
v___x_3371_ = 0;
v___x_3372_ = l_Lean_SourceInfo_fromRef(v_ref_3370_, v___x_3371_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81));
lean_inc_ref(v___x_3360_);
v___x_3374_ = l_Lean_Name_mkStr4(v___x_3360_, v___x_3361_, v___x_3362_, v___x_3373_);
v___x_3375_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__1);
v___x_3376_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___closed__2));
lean_inc_ref(v___x_3363_);
v___x_3377_ = l_Lean_Name_mkStr2(v___x_3363_, v___x_3376_);
lean_inc(v_currMacroScope_3369_);
lean_inc(v_quotContext_3368_);
v___x_3378_ = l_Lean_addMacroScope(v_quotContext_3368_, v___x_3377_, v_currMacroScope_3369_);
v___x_3379_ = l_Lean_Name_mkStr4(v___x_3360_, v___x_3364_, v___x_3363_, v___x_3376_);
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
lean_ctor_set(v___x_3382_, 1, v___x_3380_);
lean_inc_n(v___x_3372_, 2);
v___x_3383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3372_);
lean_ctor_set(v___x_3383_, 1, v___x_3375_);
lean_ctor_set(v___x_3383_, 2, v___x_3378_);
lean_ctor_set(v___x_3383_, 3, v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__command____Ensure__eval__term__expr__instances____1___closed__3));
v___x_3385_ = l_Lean_Syntax_node1(v___x_3372_, v___x_3384_, v_eval_3365_);
v___x_3386_ = l_Lean_Syntax_node2(v___x_3372_, v___x_3374_, v___x_3383_, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___y_3367_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___boxed(lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v___x_3390_, lean_object* v___x_3391_, lean_object* v___x_3392_, lean_object* v_eval_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1(v___x_3388_, v___x_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v_eval_3393_, v___y_3394_, v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3396_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__1));
v___x_3404_ = l_Lean_mkCIdent(v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1(lean_object* v_x_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3408_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__0));
v___x_3409_ = ((lean_object*)(l_Lean_Elab_ConfigEval_command____Ensure__eval__term__instance___00__closed__1));
v___x_3410_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
lean_inc(v_x_3405_);
v___x_3411_ = l_Lean_Syntax_isOfKind(v_x_3405_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v_x_3405_);
v___x_3412_ = lean_box(1);
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_a_3407_);
return v___x_3413_;
}
else
{
lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v_tk_3420_; lean_object* v___x_3421_; lean_object* v_elabName_3422_; lean_object* v___x_3423_; lean_object* v_type_3424_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___y_3474_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___f_3414_ = ((lean_object*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCoreConfigElab__1___closed__1));
v___x_3415_ = lean_unsigned_to_nat(0u);
v___x_3416_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3415_);
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3417_);
v___x_3419_ = lean_unsigned_to_nat(2u);
v_tk_3420_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3419_);
v___x_3421_ = lean_unsigned_to_nat(3u);
v_elabName_3422_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3421_);
v___x_3423_ = lean_unsigned_to_nat(4u);
v_type_3424_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3423_);
v___x_3471_ = lean_unsigned_to_nat(5u);
v___x_3472_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3471_);
v___x_3488_ = lean_unsigned_to_nat(6u);
v___x_3489_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3488_);
lean_dec(v_x_3405_);
v___x_3490_ = l_Lean_Syntax_getOptional_x3f(v___x_3489_);
lean_dec(v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_box(0);
v___y_3474_ = v___x_3491_;
goto v___jp_3473_;
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
v_val_3492_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3490_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_val_3492_);
lean_dec(v___x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_val_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
v___y_3474_ = v___x_3497_;
goto v___jp_3473_;
}
}
}
v___jp_3425_:
{
lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
lean_inc_ref(v___y_3426_);
lean_inc_ref(v___y_3427_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___lam__1___boxed), 8, 5);
lean_closure_set(v___f_3433_, 0, v___x_3408_);
lean_closure_set(v___f_3433_, 1, v___y_3427_);
lean_closure_set(v___f_3433_, 2, v___y_3426_);
lean_closure_set(v___f_3433_, 3, v___x_3432_);
lean_closure_set(v___f_3433_, 4, v___x_3409_);
v___x_3434_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___closed__2);
v___x_3435_ = lean_obj_once(&l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3, &l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3_once, _init_l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareTermConfigElab__1___closed__3);
v___x_3436_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_3434_, v___f_3433_, v___x_3435_, v___f_3414_, v___y_3431_, v___y_3429_, v_tk_3420_, v_elabName_3422_, v_type_3424_, v___y_3428_, v___y_3430_, v_a_3406_, v_a_3407_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_a_3438_ = lean_ctor_get(v___x_3436_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3436_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3437_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3446_ = lean_ctor_get(v___x_3436_, 0);
v_a_3447_ = lean_ctor_get(v___x_3436_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3436_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_inc(v_a_3446_);
lean_dec(v___x_3436_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3446_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
v___jp_3455_:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Syntax_getOptional_x3f(v___x_3416_);
lean_dec(v___x_3416_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
v___y_3426_ = v___y_3456_;
v___y_3427_ = v___y_3457_;
v___y_3428_ = v___y_3459_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___y_3458_;
v___y_3431_ = v___x_3462_;
goto v___jp_3425_;
}
else
{
lean_object* v_val_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_val_3463_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3461_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_val_3463_);
lean_dec(v___x_3461_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_val_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v___y_3426_ = v___y_3456_;
v___y_3427_ = v___y_3457_;
v___y_3428_ = v___y_3459_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___y_3458_;
v___y_3431_ = v___x_3468_;
goto v___jp_3425_;
}
}
}
}
v___jp_3473_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v_binders_3477_; lean_object* v___x_3478_; 
v___x_3475_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0));
v___x_3476_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
v_binders_3477_ = l_Lean_Syntax_getArgs(v___x_3472_);
lean_dec(v___x_3472_);
v___x_3478_ = l_Lean_Syntax_getOptional_x3f(v___x_3418_);
lean_dec(v___x_3418_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_box(0);
v___y_3456_ = v___x_3476_;
v___y_3457_ = v___x_3475_;
v___y_3458_ = v___y_3474_;
v___y_3459_ = v_binders_3477_;
v___y_3460_ = v___x_3479_;
goto v___jp_3455_;
}
else
{
lean_object* v_val_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
v_val_3480_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3478_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_val_3480_);
lean_dec(v___x_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_val_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
v___y_3456_ = v___x_3476_;
v___y_3457_ = v___x_3475_;
v___y_3458_ = v___y_3474_;
v___y_3459_ = v_binders_3477_;
v___y_3460_ = v___x_3485_;
goto v___jp_3455_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1___boxed(lean_object* v_x_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Elab_ConfigEval___aux__Lean__Elab__ConfigEval__Commands______macroRules__Lean__Elab__ConfigEval__elabDeclareCommandConfig__1(v_x_3500_, v_a_3501_, v_a_3502_);
lean_dec_ref(v_a_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_3508_, v___x_3509_, v_a_3504_, v_a_3505_, v_a_3506_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab(v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
return v_res_3515_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed), 4, 0);
v___x_3517_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3517_, 0, v___x_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
v___x_3520_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0);
v___x_3521_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3519_, v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
return v_res_3523_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_MissingDocs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Commands_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_ConfigEval_configEntryOmit = _init_l_Lean_Elab_ConfigEval_configEntryOmit();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntryOmit);
l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix = _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix);
l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard = _init_l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard);
l_Lean_Elab_ConfigEval_configEntryHandlerKey = _init_l_Lean_Elab_ConfigEval_configEntryHandlerKey();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntryHandlerKey);
l_Lean_Elab_ConfigEval_configEntryHandler = _init_l_Lean_Elab_ConfigEval_configEntryHandler();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntryHandler);
l_Lean_Elab_ConfigEval_configEntry = _init_l_Lean_Elab_ConfigEval_configEntry();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntry);
l_Lean_Elab_ConfigEval_configEntries = _init_l_Lean_Elab_ConfigEval_configEntries();
lean_mark_persistent(l_Lean_Elab_ConfigEval_configEntries);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Commands(builtin);
}
#ifdef __cplusplus
}
#endif
