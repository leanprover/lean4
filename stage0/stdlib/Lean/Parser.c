// Lean compiler output
// Module: Lean.Parser
// Imports: public import Lean.Parser.Basic public import Lean.Parser.Level public import Lean.Parser.Term public import Lean.Parser.Tactic public import Lean.Parser.Command public import Lean.Parser.Module public import Lean.Parser.Syntax public import Lean.Parser.Do public import Lean.Parser.Tactic.Doc
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
lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l_Lean_Parser_Term_num_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_Term_str_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_Term_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_scientificLit;
lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookahead(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Parser_checkLineEq(lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hexnum;
lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hygieneInfo;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_rawIdent;
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 198, 251, 95, 67, 81, 118, 246)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "notFollowedBy"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 55, 249, 172, 87, 126, 186, 81)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 0, 133, 48, 146, 73, 208, 113)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 177, 38, 2, 101, 67, 237, 158)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 137, 49, 69, 62, 133, 213, 34)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_recover, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 226, 49, 74, 122, 217, 187, 147)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_andthen, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 70, 47, 117, 238, 126, 239, 49)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_orelse, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 234, 249, 199, 49, 244, 72, 166)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 182, 82, 21, 251, 127, 209, 38)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_interpolatedStr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 202, 249, 244, 227, 198, 135, 34)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 23, 219, 174, 6, 42, 106, 219)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 222, 221, 61, 47, 46, 252, 242)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 188, 255, 221, 143, 31, 128, 82)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withPosition, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "checkWsBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 180, 243, 53, 77, 82, 55, 205)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "space before"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 167, 191, 130, 216, 220, 182, 40)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "many1Indent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 232, 149, 52, 5, 17, 36, 232)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 214, 77, 50, 137, 69, 220, 172)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1Indent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1Indent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "manyIndent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 35, 49, 198, 227, 245, 222, 169)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 71, 18, 147, 220, 40, 152, 21)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_manyIndent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_manyIndent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 61, 196, 93, 201, 246, 193, 192)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 114, 232, 230, 181, 52, 168, 160)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 16, 254, 130, 153, 255, 99, 153)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 94, 230, 204, 13, 59, 242, 46)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 19, 60, 201, 90, 143, 111, 211)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_lookahead, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lineEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 222, 52, 211, 142, 186, 26, 103)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkLineEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 130, 255, 142, 22, 38, 200, 197)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 155, 248, 3, 115, 223, 12, 139)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 79, 136, 97, 27, 86, 56, 4)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGe"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 21, 222, 233, 68, 88, 239, 150)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGt"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 27, 6, 116, 51, 223, 220, 245)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 96, 174, 177, 221, 86, 223, 51)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_hygieneInfo_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_hygieneInfo_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rawIdent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 100, 176, 236, 81, 164, 232, 12)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 2, 179, 39, 67, 204, 226, 154)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 242, 101, 31, 193, 156, 127, 171)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "scientificLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 25, 249, 160, 8, 56, 13, 159)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_scientificLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_scientificLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nameLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 229, 203, 158, 195, 74, 86, 122)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nameLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nameLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "charLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 82, 20, 217, 44, 105, 253, 153)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_charLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_charLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 157, 94, 66, 135, 29, 115, 44)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "numLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 124, 25, 195, 9, 201, 171, 221)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 147, 100, 44, 136, 108, 159, 66)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "checkLinebreakBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 136, 117, 184, 203, 101, 193, 45)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkNoWsBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 175, 148, 38, 136, 238, 167, 124)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Parenthesizer"};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value;
static const lean_string_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 80, 206, 144, 206, 86, 123, 88)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 233, 14, 51, 59, 26, 143, 93)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(184, 151, 240, 167, 197, 64, 62, 10)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_num_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 80, 206, 144, 206, 86, 123, 88)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 160, 160, 165, 225, 137, 109, 89)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 17, 139, 185, 158, 246, 57, 95)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_scientific_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 80, 206, 144, 206, 86, 123, 88)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 169, 213, 135, 193, 195, 181, 162)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 74, 105, 254, 5, 48, 59, 254)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_char_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 80, 206, 144, 206, 86, 123, 88)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 21, 185, 140, 206, 31, 0, 27)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 126, 106, 230, 172, 96, 250, 51)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_str_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 80, 206, 144, 206, 86, 123, 88)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 61, 18, 10, 61, 249, 234, 173)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(179, 91, 7, 25, 4, 156, 230, 12)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Formatter"};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 65, 136, 208, 75, 168, 22, 8)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 7, 102, 176, 201, 50, 36, 151)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 43, 34, 89, 148, 124, 12, 72)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_num_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 65, 136, 208, 75, 168, 22, 8)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 145, 199, 126, 121, 58, 89, 39)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(126, 226, 141, 140, 1, 167, 133, 167)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_scientific_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 65, 136, 208, 75, 168, 22, 8)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 39, 82, 251, 165, 33, 85, 105)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 112, 121, 124, 112, 87, 30, 19)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_char_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 65, 136, 208, 75, 168, 22, 8)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 247, 13, 105, 80, 134, 66, 66)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 156, 14, 253, 87, 33, 89, 10)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_str_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 65, 136, 208, 75, 168, 22, 8)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 191, 21, 76, 153, 54, 88, 65)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 22, 145, 4, 145, 86, 25, 230)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_2_);
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1_, v___y_2_, v___y_3_, v___y_4_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_8_, v___y_9_, v___y_10_, v___y_11_);
lean_dec(v___y_11_);
lean_dec_ref(v___y_10_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
return v_res_13_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_5(v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, lean_box(0));
return v___x_20_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_14_ = stack[0].m_obj;
lean_object* v___y_15_ = stack[1].m_obj;
lean_object* v___y_16_ = stack[2].m_obj;
lean_object* v___y_17_ = stack[3].m_obj;
lean_object* v___y_18_ = stack[4].m_obj;
lean_object* v_res_21_;
v_res_21_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
return v_res_28_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_31_ = l_Lean_Parser_checkColGe(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_34_ = l_Lean_Parser_andthen(v___x_33_, v___y_32_);
v___x_35_ = l_Lean_Parser_many(v___x_34_);
v___x_36_ = l_Lean_Parser_withPosition(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_38_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_39_ = l_Lean_Parser_andthen(v___x_38_, v___y_37_);
v___x_40_ = l_Lean_Parser_many1(v___x_39_);
v___x_41_ = l_Lean_Parser_withPosition(v___x_40_);
return v___x_41_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_43_);
return v___x_47_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v___y_44_ = stack[2].m_obj;
lean_object* v___y_45_ = stack[3].m_obj;
lean_object* v_res_48_;
v_res_48_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_42_, v___y_43_, v___y_44_, v___y_45_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_5(v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_55_ = stack[0].m_obj;
lean_object* v___y_56_ = stack[1].m_obj;
lean_object* v___y_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v___y_59_ = stack[4].m_obj;
lean_object* v_res_62_;
v_res_62_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_73_ = l_Lean_Parser_notFollowedBy(v_x_71_, v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = l_Lean_Parser_hexnum;
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed), 5, 0);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_250_ = l_Lean_Parser_checkWsBefore(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_395_ = l_Lean_Parser_checkLineEq(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_413_ = l_Lean_Parser_checkColEq(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed), 5, 0);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_431_ = l_Lean_Parser_checkColGe(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_449_ = l_Lean_Parser_checkColGt(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = l_Lean_Parser_hygieneInfo;
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = l_Lean_Parser_rawIdent;
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = l_Lean_Parser_ident;
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = l_Lean_Parser_scientificLit;
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_Lean_Parser_nameLit;
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = l_Lean_Parser_charLit;
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = l_Lean_Parser_strLit;
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Parser_numLit;
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_613_ = l_Lean_Parser_checkLinebreakBefore(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_632_ = l_Lean_Parser_checkNoWsBefore(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed), 5, 0);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed), 5, 0);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_646_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; uint8_t v___y_816_; lean_object* v___y_817_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___x_857_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1015_; lean_object* v___y_1028_; lean_object* v___y_1039_; lean_object* v___x_1049_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_762_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_763_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_764_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_765_ = lean_box(0);
v___x_857_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1049_ = l_Lean_Parser_registerAlias(v___x_646_, v___x_762_, v___x_763_, v___x_764_, v___x_857_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref_known(v___x_1049_, 1);
v___x_1050_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1051_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_646_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref_known(v___x_1051_, 1);
v___x_1052_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1053_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_646_, v___x_1052_);
v___y_1039_ = v___x_1053_;
goto v___jp_1038_;
}
else
{
v___y_1039_ = v___x_1051_;
goto v___jp_1038_;
}
}
else
{
v___y_1039_ = v___x_1049_;
goto v___jp_1038_;
}
v___jp_647_:
{
if (lean_obj_tag(v___y_649_) == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v___y_649_, 1);
v___x_650_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_651_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_652_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_653_ = lean_box(0);
v___x_654_ = l_Lean_Parser_registerAlias(v___x_650_, v___x_651_, v___x_652_, v___x_653_, v___y_648_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec_ref_known(v___x_654_, 1);
v___x_655_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_656_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_650_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref_known(v___x_656_, 1);
v___x_657_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_658_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_650_, v___x_657_);
return v___x_658_;
}
else
{
return v___x_656_;
}
}
else
{
return v___x_654_;
}
}
else
{
lean_dec_ref(v___y_648_);
return v___y_649_;
}
}
v___jp_659_:
{
if (lean_obj_tag(v___y_661_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref_known(v___y_661_, 1);
v___x_662_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_663_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_664_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_665_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_660_);
v___x_666_ = l_Lean_Parser_registerAlias(v___x_662_, v___x_663_, v___x_664_, v___x_665_, v___y_660_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_666_, 1);
v___x_667_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_668_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_662_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref_known(v___x_668_, 1);
v___x_669_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_670_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_662_, v___x_669_);
v___y_648_ = v___y_660_;
v___y_649_ = v___x_670_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___y_660_;
v___y_649_ = v___x_668_;
goto v___jp_647_;
}
}
else
{
v___y_648_ = v___y_660_;
v___y_649_ = v___x_666_;
goto v___jp_647_;
}
}
else
{
lean_dec_ref(v___y_660_);
return v___y_661_;
}
}
v___jp_671_:
{
if (lean_obj_tag(v___y_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref_known(v___y_674_, 1);
v___x_675_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_676_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_677_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_678_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_679_ = l_Lean_Parser_registerAlias(v___x_675_, v___x_676_, v___x_677_, v___x_678_, v___y_672_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_679_, 1);
v___x_680_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_681_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_675_, v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref_known(v___x_681_, 1);
v___x_682_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_683_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_675_, v___x_682_);
v___y_660_ = v___y_673_;
v___y_661_ = v___x_683_;
goto v___jp_659_;
}
else
{
v___y_660_ = v___y_673_;
v___y_661_ = v___x_681_;
goto v___jp_659_;
}
}
else
{
v___y_660_ = v___y_673_;
v___y_661_ = v___x_679_;
goto v___jp_659_;
}
}
else
{
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
return v___y_674_;
}
}
v___jp_684_:
{
if (lean_obj_tag(v___y_687_) == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref_known(v___y_687_, 1);
v___x_688_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_689_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_690_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_691_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_686_);
v___x_692_ = l_Lean_Parser_registerAlias(v___x_688_, v___x_689_, v___x_690_, v___x_691_, v___y_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref_known(v___x_692_, 1);
v___x_693_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_694_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_688_, v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref_known(v___x_694_, 1);
v___x_695_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_696_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_688_, v___x_695_);
v___y_672_ = v___y_685_;
v___y_673_ = v___y_686_;
v___y_674_ = v___x_696_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___y_685_;
v___y_673_ = v___y_686_;
v___y_674_ = v___x_694_;
goto v___jp_671_;
}
}
else
{
v___y_672_ = v___y_685_;
v___y_673_ = v___y_686_;
v___y_674_ = v___x_692_;
goto v___jp_671_;
}
}
else
{
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
return v___y_687_;
}
}
v___jp_697_:
{
if (lean_obj_tag(v___y_700_) == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec_ref_known(v___y_700_, 1);
v___x_701_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_702_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_703_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_704_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_699_);
v___x_705_ = l_Lean_Parser_registerAlias(v___x_701_, v___x_702_, v___x_703_, v___x_704_, v___y_699_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec_ref_known(v___x_705_, 1);
v___x_706_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_707_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_701_, v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref_known(v___x_707_, 1);
v___x_708_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_709_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_701_, v___x_708_);
v___y_685_ = v___y_698_;
v___y_686_ = v___y_699_;
v___y_687_ = v___x_709_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___y_699_;
v___y_687_ = v___x_707_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___y_699_;
v___y_687_ = v___x_705_;
goto v___jp_684_;
}
}
else
{
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_698_);
return v___y_700_;
}
}
v___jp_710_:
{
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec_ref_known(v___y_713_, 1);
v___x_714_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_715_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_716_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_717_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_712_);
v___x_718_ = l_Lean_Parser_registerAlias(v___x_714_, v___x_715_, v___x_716_, v___x_717_, v___y_712_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref_known(v___x_718_, 1);
v___x_719_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_720_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_714_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref_known(v___x_720_, 1);
v___x_721_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_722_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_714_, v___x_721_);
v___y_698_ = v___y_711_;
v___y_699_ = v___y_712_;
v___y_700_ = v___x_722_;
goto v___jp_697_;
}
else
{
v___y_698_ = v___y_711_;
v___y_699_ = v___y_712_;
v___y_700_ = v___x_720_;
goto v___jp_697_;
}
}
else
{
v___y_698_ = v___y_711_;
v___y_699_ = v___y_712_;
v___y_700_ = v___x_718_;
goto v___jp_697_;
}
}
else
{
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
return v___y_713_;
}
}
v___jp_723_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref_known(v___y_726_, 1);
v___x_727_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_728_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_729_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_730_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_724_);
v___x_731_ = l_Lean_Parser_registerAlias(v___x_727_, v___x_728_, v___x_729_, v___x_730_, v___y_724_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref_known(v___x_731_, 1);
v___x_732_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_733_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_727_, v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref_known(v___x_733_, 1);
v___x_734_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_735_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_727_, v___x_734_);
v___y_711_ = v___y_724_;
v___y_712_ = v___y_725_;
v___y_713_ = v___x_735_;
goto v___jp_710_;
}
else
{
v___y_711_ = v___y_724_;
v___y_712_ = v___y_725_;
v___y_713_ = v___x_733_;
goto v___jp_710_;
}
}
else
{
v___y_711_ = v___y_724_;
v___y_712_ = v___y_725_;
v___y_713_ = v___x_731_;
goto v___jp_710_;
}
}
else
{
lean_dec_ref(v___y_725_);
lean_dec_ref(v___y_724_);
return v___y_726_;
}
}
v___jp_736_:
{
if (lean_obj_tag(v___y_739_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref_known(v___y_739_, 1);
v___x_740_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_741_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_742_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_743_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_737_);
v___x_744_ = l_Lean_Parser_registerAlias(v___x_740_, v___x_741_, v___x_742_, v___x_743_, v___y_737_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref_known(v___x_744_, 1);
v___x_745_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_746_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_740_, v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_747_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_748_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_740_, v___x_747_);
v___y_724_ = v___y_737_;
v___y_725_ = v___y_738_;
v___y_726_ = v___x_748_;
goto v___jp_723_;
}
else
{
v___y_724_ = v___y_737_;
v___y_725_ = v___y_738_;
v___y_726_ = v___x_746_;
goto v___jp_723_;
}
}
else
{
v___y_724_ = v___y_737_;
v___y_725_ = v___y_738_;
v___y_726_ = v___x_744_;
goto v___jp_723_;
}
}
else
{
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_737_);
return v___y_739_;
}
}
v___jp_749_:
{
if (lean_obj_tag(v___y_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref_known(v___y_752_, 1);
v___x_753_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_754_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_755_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_756_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_750_);
v___x_757_ = l_Lean_Parser_registerAlias(v___x_753_, v___x_754_, v___x_755_, v___x_756_, v___y_750_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref_known(v___x_757_, 1);
v___x_758_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_759_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_753_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref_known(v___x_759_, 1);
v___x_760_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_761_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_753_, v___x_760_);
v___y_737_ = v___y_750_;
v___y_738_ = v___y_751_;
v___y_739_ = v___x_761_;
goto v___jp_736_;
}
else
{
v___y_737_ = v___y_750_;
v___y_738_ = v___y_751_;
v___y_739_ = v___x_759_;
goto v___jp_736_;
}
}
else
{
v___y_737_ = v___y_750_;
v___y_738_ = v___y_751_;
v___y_739_ = v___x_757_;
goto v___jp_736_;
}
}
else
{
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_750_);
return v___y_752_;
}
}
v___jp_766_:
{
if (lean_obj_tag(v___y_771_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref_known(v___y_771_, 1);
v___x_772_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_773_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_774_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_775_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc(v___y_767_);
v___x_776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_776_, 0, v___x_765_);
lean_ctor_set(v___x_776_, 1, v___y_767_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*2, v___y_770_);
v___x_777_ = l_Lean_Parser_registerAlias(v___x_772_, v___x_773_, v___x_774_, v___x_775_, v___x_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref_known(v___x_777_, 1);
v___x_778_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_779_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_772_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_781_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_772_, v___x_780_);
v___y_750_ = v___y_768_;
v___y_751_ = v___y_769_;
v___y_752_ = v___x_781_;
goto v___jp_749_;
}
else
{
v___y_750_ = v___y_768_;
v___y_751_ = v___y_769_;
v___y_752_ = v___x_779_;
goto v___jp_749_;
}
}
else
{
v___y_750_ = v___y_768_;
v___y_751_ = v___y_769_;
v___y_752_ = v___x_777_;
goto v___jp_749_;
}
}
else
{
lean_dec_ref(v___y_769_);
lean_dec_ref(v___y_768_);
return v___y_771_;
}
}
v___jp_782_:
{
if (lean_obj_tag(v___y_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref_known(v___y_787_, 1);
v___x_788_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_789_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_790_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_791_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_785_);
v___x_792_ = l_Lean_Parser_registerAlias(v___x_788_, v___x_789_, v___x_790_, v___x_791_, v___y_785_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_794_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_788_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_796_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_788_, v___x_795_);
v___y_767_ = v___y_783_;
v___y_768_ = v___y_784_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_786_;
v___y_771_ = v___x_796_;
goto v___jp_766_;
}
else
{
v___y_767_ = v___y_783_;
v___y_768_ = v___y_784_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_786_;
v___y_771_ = v___x_794_;
goto v___jp_766_;
}
}
else
{
v___y_767_ = v___y_783_;
v___y_768_ = v___y_784_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_786_;
v___y_771_ = v___x_792_;
goto v___jp_766_;
}
}
else
{
lean_dec_ref(v___y_785_);
lean_dec_ref(v___y_784_);
return v___y_787_;
}
}
v___jp_797_:
{
if (lean_obj_tag(v___y_802_) == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref_known(v___y_802_, 1);
v___x_803_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_804_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_805_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_806_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_800_);
v___x_807_ = l_Lean_Parser_registerAlias(v___x_803_, v___x_804_, v___x_805_, v___x_806_, v___y_800_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref_known(v___x_807_, 1);
v___x_808_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_809_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_803_, v___x_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref_known(v___x_809_, 1);
v___x_810_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_811_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_803_, v___x_810_);
v___y_783_ = v___y_798_;
v___y_784_ = v___y_799_;
v___y_785_ = v___y_800_;
v___y_786_ = v___y_801_;
v___y_787_ = v___x_811_;
goto v___jp_782_;
}
else
{
v___y_783_ = v___y_798_;
v___y_784_ = v___y_799_;
v___y_785_ = v___y_800_;
v___y_786_ = v___y_801_;
v___y_787_ = v___x_809_;
goto v___jp_782_;
}
}
else
{
v___y_783_ = v___y_798_;
v___y_784_ = v___y_799_;
v___y_785_ = v___y_800_;
v___y_786_ = v___y_801_;
v___y_787_ = v___x_807_;
goto v___jp_782_;
}
}
else
{
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_799_);
return v___y_802_;
}
}
v___jp_812_:
{
if (lean_obj_tag(v___y_817_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref_known(v___y_817_, 1);
v___x_818_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_819_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_820_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_821_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_815_);
v___x_822_ = l_Lean_Parser_registerAlias(v___x_818_, v___x_819_, v___x_820_, v___x_821_, v___y_815_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref_known(v___x_822_, 1);
v___x_823_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_824_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_818_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref_known(v___x_824_, 1);
v___x_825_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_826_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_818_, v___x_825_);
v___y_798_ = v___y_813_;
v___y_799_ = v___y_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___y_816_;
v___y_802_ = v___x_826_;
goto v___jp_797_;
}
else
{
v___y_798_ = v___y_813_;
v___y_799_ = v___y_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___y_816_;
v___y_802_ = v___x_824_;
goto v___jp_797_;
}
}
else
{
v___y_798_ = v___y_813_;
v___y_799_ = v___y_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___y_816_;
v___y_802_ = v___x_822_;
goto v___jp_797_;
}
}
else
{
lean_dec_ref(v___y_815_);
lean_dec_ref(v___y_814_);
return v___y_817_;
}
}
v___jp_827_:
{
if (lean_obj_tag(v___y_832_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref_known(v___y_832_, 1);
v___x_833_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_834_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_835_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_836_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_830_);
v___x_837_ = l_Lean_Parser_registerAlias(v___x_833_, v___x_834_, v___x_835_, v___x_836_, v___y_830_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_837_, 1);
v___x_838_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_839_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_833_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref_known(v___x_839_, 1);
v___x_840_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_841_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_833_, v___x_840_);
v___y_813_ = v___y_828_;
v___y_814_ = v___y_829_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_831_;
v___y_817_ = v___x_841_;
goto v___jp_812_;
}
else
{
v___y_813_ = v___y_828_;
v___y_814_ = v___y_829_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_831_;
v___y_817_ = v___x_839_;
goto v___jp_812_;
}
}
else
{
v___y_813_ = v___y_828_;
v___y_814_ = v___y_829_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_831_;
v___y_817_ = v___x_837_;
goto v___jp_812_;
}
}
else
{
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
return v___y_832_;
}
}
v___jp_842_:
{
if (lean_obj_tag(v___y_845_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v___y_845_, 1);
v___x_846_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_847_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_848_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_849_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_850_ = 0;
v___x_851_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_852_ = l_Lean_Parser_registerAlias(v___x_846_, v___x_847_, v___x_848_, v___x_849_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_853_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_854_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_846_, v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref_known(v___x_854_, 1);
v___x_855_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_856_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_846_, v___x_855_);
v___y_828_ = v___y_843_;
v___y_829_ = v___x_851_;
v___y_830_ = v___y_844_;
v___y_831_ = v___x_850_;
v___y_832_ = v___x_856_;
goto v___jp_827_;
}
else
{
v___y_828_ = v___y_843_;
v___y_829_ = v___x_851_;
v___y_830_ = v___y_844_;
v___y_831_ = v___x_850_;
v___y_832_ = v___x_854_;
goto v___jp_827_;
}
}
else
{
v___y_828_ = v___y_843_;
v___y_829_ = v___x_851_;
v___y_830_ = v___y_844_;
v___y_831_ = v___x_850_;
v___y_832_ = v___x_852_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v___y_844_);
return v___y_845_;
}
}
v___jp_858_:
{
if (lean_obj_tag(v___y_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref_known(v___y_861_, 1);
v___x_862_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_863_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_864_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_865_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_866_ = l_Lean_Parser_registerAlias(v___x_862_, v___x_863_, v___x_864_, v___x_865_, v___x_857_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref_known(v___x_866_, 1);
v___x_867_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_868_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_862_, v___x_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref_known(v___x_868_, 1);
v___x_869_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_870_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_862_, v___x_869_);
v___y_843_ = v___y_859_;
v___y_844_ = v___y_860_;
v___y_845_ = v___x_870_;
goto v___jp_842_;
}
else
{
v___y_843_ = v___y_859_;
v___y_844_ = v___y_860_;
v___y_845_ = v___x_868_;
goto v___jp_842_;
}
}
else
{
v___y_843_ = v___y_859_;
v___y_844_ = v___y_860_;
v___y_845_ = v___x_866_;
goto v___jp_842_;
}
}
else
{
lean_dec_ref(v___y_860_);
return v___y_861_;
}
}
v___jp_871_:
{
if (lean_obj_tag(v___y_874_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec_ref_known(v___y_874_, 1);
v___x_875_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_876_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_877_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_878_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_879_ = l_Lean_Parser_registerAlias(v___x_875_, v___x_876_, v___x_877_, v___x_878_, v___x_857_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_881_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_875_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref_known(v___x_881_, 1);
v___x_882_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_883_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_875_, v___x_882_);
v___y_859_ = v___y_872_;
v___y_860_ = v___y_873_;
v___y_861_ = v___x_883_;
goto v___jp_858_;
}
else
{
v___y_859_ = v___y_872_;
v___y_860_ = v___y_873_;
v___y_861_ = v___x_881_;
goto v___jp_858_;
}
}
else
{
v___y_859_ = v___y_872_;
v___y_860_ = v___y_873_;
v___y_861_ = v___x_879_;
goto v___jp_858_;
}
}
else
{
lean_dec_ref(v___y_873_);
return v___y_874_;
}
}
v___jp_884_:
{
if (lean_obj_tag(v___y_887_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___y_887_, 1);
v___x_888_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_889_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_890_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_891_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_892_ = l_Lean_Parser_registerAlias(v___x_888_, v___x_889_, v___x_890_, v___x_891_, v___x_857_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref_known(v___x_892_, 1);
v___x_893_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_894_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_888_, v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref_known(v___x_894_, 1);
v___x_895_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_896_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_888_, v___x_895_);
v___y_872_ = v___y_885_;
v___y_873_ = v___y_886_;
v___y_874_ = v___x_896_;
goto v___jp_871_;
}
else
{
v___y_872_ = v___y_885_;
v___y_873_ = v___y_886_;
v___y_874_ = v___x_894_;
goto v___jp_871_;
}
}
else
{
v___y_872_ = v___y_885_;
v___y_873_ = v___y_886_;
v___y_874_ = v___x_892_;
goto v___jp_871_;
}
}
else
{
lean_dec_ref(v___y_886_);
return v___y_887_;
}
}
v___jp_897_:
{
if (lean_obj_tag(v___y_900_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec_ref_known(v___y_900_, 1);
v___x_901_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_902_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_903_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_904_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_905_ = l_Lean_Parser_registerAlias(v___x_901_, v___x_902_, v___x_903_, v___x_904_, v___x_857_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref_known(v___x_905_, 1);
v___x_906_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_907_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_901_, v___x_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_908_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_909_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_901_, v___x_908_);
v___y_885_ = v___y_898_;
v___y_886_ = v___y_899_;
v___y_887_ = v___x_909_;
goto v___jp_884_;
}
else
{
v___y_885_ = v___y_898_;
v___y_886_ = v___y_899_;
v___y_887_ = v___x_907_;
goto v___jp_884_;
}
}
else
{
v___y_885_ = v___y_898_;
v___y_886_ = v___y_899_;
v___y_887_ = v___x_905_;
goto v___jp_884_;
}
}
else
{
lean_dec_ref(v___y_899_);
return v___y_900_;
}
}
v___jp_910_:
{
if (lean_obj_tag(v___y_913_) == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref_known(v___y_913_, 1);
v___x_914_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_915_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_916_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_917_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_918_ = l_Lean_Parser_registerAlias(v___x_914_, v___x_915_, v___x_916_, v___x_917_, v___x_857_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_919_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_920_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_914_, v___x_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_921_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_922_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_914_, v___x_921_);
v___y_898_ = v___y_911_;
v___y_899_ = v___y_912_;
v___y_900_ = v___x_922_;
goto v___jp_897_;
}
else
{
v___y_898_ = v___y_911_;
v___y_899_ = v___y_912_;
v___y_900_ = v___x_920_;
goto v___jp_897_;
}
}
else
{
v___y_898_ = v___y_911_;
v___y_899_ = v___y_912_;
v___y_900_ = v___x_918_;
goto v___jp_897_;
}
}
else
{
lean_dec_ref(v___y_912_);
return v___y_913_;
}
}
v___jp_923_:
{
if (lean_obj_tag(v___y_926_) == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref_known(v___y_926_, 1);
v___x_927_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_928_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_929_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_930_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_925_);
v___x_931_ = l_Lean_Parser_registerAlias(v___x_927_, v___x_928_, v___x_929_, v___x_930_, v___y_925_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref_known(v___x_931_, 1);
v___x_932_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_933_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_927_, v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref_known(v___x_933_, 1);
v___x_934_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_935_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_927_, v___x_934_);
v___y_911_ = v___y_924_;
v___y_912_ = v___y_925_;
v___y_913_ = v___x_935_;
goto v___jp_910_;
}
else
{
v___y_911_ = v___y_924_;
v___y_912_ = v___y_925_;
v___y_913_ = v___x_933_;
goto v___jp_910_;
}
}
else
{
v___y_911_ = v___y_924_;
v___y_912_ = v___y_925_;
v___y_913_ = v___x_931_;
goto v___jp_910_;
}
}
else
{
lean_dec_ref(v___y_925_);
return v___y_926_;
}
}
v___jp_936_:
{
if (lean_obj_tag(v___y_940_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref_known(v___y_940_, 1);
v___x_941_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_942_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_943_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
lean_inc_ref(v___y_938_);
v___x_944_ = l_Lean_Parser_registerAlias(v___x_941_, v___x_942_, v___x_943_, v___y_939_, v___y_938_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec_ref_known(v___x_944_, 1);
v___x_945_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_946_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_941_, v___x_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec_ref_known(v___x_946_, 1);
v___x_947_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_948_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_941_, v___x_947_);
v___y_924_ = v___y_937_;
v___y_925_ = v___y_938_;
v___y_926_ = v___x_948_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_937_;
v___y_925_ = v___y_938_;
v___y_926_ = v___x_946_;
goto v___jp_923_;
}
}
else
{
v___y_924_ = v___y_937_;
v___y_925_ = v___y_938_;
v___y_926_ = v___x_944_;
goto v___jp_923_;
}
}
else
{
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v___y_940_;
}
}
v___jp_949_:
{
if (lean_obj_tag(v___y_952_) == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref_known(v___y_952_, 1);
v___x_953_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_954_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_955_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_956_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_951_);
v___x_957_ = l_Lean_Parser_registerAlias(v___x_953_, v___x_954_, v___x_955_, v___x_956_, v___y_951_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec_ref_known(v___x_957_, 1);
v___x_958_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_959_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_953_, v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref_known(v___x_959_, 1);
v___x_960_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_961_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_953_, v___x_960_);
v___y_937_ = v___y_950_;
v___y_938_ = v___y_951_;
v___y_939_ = v___x_956_;
v___y_940_ = v___x_961_;
goto v___jp_936_;
}
else
{
v___y_937_ = v___y_950_;
v___y_938_ = v___y_951_;
v___y_939_ = v___x_956_;
v___y_940_ = v___x_959_;
goto v___jp_936_;
}
}
else
{
v___y_937_ = v___y_950_;
v___y_938_ = v___y_951_;
v___y_939_ = v___x_956_;
v___y_940_ = v___x_957_;
goto v___jp_936_;
}
}
else
{
lean_dec_ref(v___y_951_);
return v___y_952_;
}
}
v___jp_962_:
{
if (lean_obj_tag(v___y_965_) == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref_known(v___y_965_, 1);
v___x_966_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_967_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_968_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_969_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_964_);
v___x_970_ = l_Lean_Parser_registerAlias(v___x_966_, v___x_967_, v___x_968_, v___x_969_, v___y_964_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref_known(v___x_970_, 1);
v___x_971_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_972_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_966_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_974_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_966_, v___x_973_);
v___y_950_ = v___y_963_;
v___y_951_ = v___y_964_;
v___y_952_ = v___x_974_;
goto v___jp_949_;
}
else
{
v___y_950_ = v___y_963_;
v___y_951_ = v___y_964_;
v___y_952_ = v___x_972_;
goto v___jp_949_;
}
}
else
{
v___y_950_ = v___y_963_;
v___y_951_ = v___y_964_;
v___y_952_ = v___x_970_;
goto v___jp_949_;
}
}
else
{
lean_dec_ref(v___y_964_);
return v___y_965_;
}
}
v___jp_975_:
{
if (lean_obj_tag(v___y_978_) == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec_ref_known(v___y_978_, 1);
v___x_979_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_980_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_981_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_982_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_977_);
v___x_983_ = l_Lean_Parser_registerAlias(v___x_979_, v___x_980_, v___x_981_, v___x_982_, v___y_977_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref_known(v___x_983_, 1);
v___x_984_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_985_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_979_, v___x_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref_known(v___x_985_, 1);
v___x_986_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_987_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_979_, v___x_986_);
v___y_963_ = v___y_976_;
v___y_964_ = v___y_977_;
v___y_965_ = v___x_987_;
goto v___jp_962_;
}
else
{
v___y_963_ = v___y_976_;
v___y_964_ = v___y_977_;
v___y_965_ = v___x_985_;
goto v___jp_962_;
}
}
else
{
v___y_963_ = v___y_976_;
v___y_964_ = v___y_977_;
v___y_965_ = v___x_983_;
goto v___jp_962_;
}
}
else
{
lean_dec_ref(v___y_977_);
return v___y_978_;
}
}
v___jp_988_:
{
if (lean_obj_tag(v___y_991_) == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec_ref_known(v___y_991_, 1);
v___x_992_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_993_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_994_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_995_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_990_);
v___x_996_ = l_Lean_Parser_registerAlias(v___x_992_, v___x_993_, v___x_994_, v___x_995_, v___y_990_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_997_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_998_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_992_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_998_, 1);
v___x_999_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1000_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_992_, v___x_999_);
v___y_976_ = v___y_989_;
v___y_977_ = v___y_990_;
v___y_978_ = v___x_1000_;
goto v___jp_975_;
}
else
{
v___y_976_ = v___y_989_;
v___y_977_ = v___y_990_;
v___y_978_ = v___x_998_;
goto v___jp_975_;
}
}
else
{
v___y_976_ = v___y_989_;
v___y_977_ = v___y_990_;
v___y_978_ = v___x_996_;
goto v___jp_975_;
}
}
else
{
lean_dec_ref(v___y_990_);
return v___y_991_;
}
}
v___jp_1001_:
{
if (lean_obj_tag(v___y_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref_known(v___y_1004_, 1);
v___x_1005_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1006_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1007_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
lean_inc_ref(v___y_1003_);
v___x_1009_ = l_Lean_Parser_registerAlias(v___x_1005_, v___x_1006_, v___x_1007_, v___x_1008_, v___y_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___x_1009_, 1);
v___x_1010_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1011_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_1005_, v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec_ref_known(v___x_1011_, 1);
v___x_1012_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1013_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_1005_, v___x_1012_);
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1003_;
v___y_991_ = v___x_1013_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1003_;
v___y_991_ = v___x_1011_;
goto v___jp_988_;
}
}
else
{
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1003_;
v___y_991_ = v___x_1009_;
goto v___jp_988_;
}
}
else
{
lean_dec_ref(v___y_1003_);
return v___y_1004_;
}
}
v___jp_1014_:
{
if (lean_obj_tag(v___y_1015_) == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref_known(v___y_1015_, 1);
v___x_1016_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1017_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1018_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1020_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1021_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1022_ = l_Lean_Parser_registerAlias(v___x_1016_, v___x_1017_, v___x_1018_, v___x_1019_, v___x_1021_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref_known(v___x_1022_, 1);
v___x_1023_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1024_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_1016_, v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref_known(v___x_1024_, 1);
v___x_1025_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1026_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_1016_, v___x_1025_);
v___y_1002_ = v___x_1020_;
v___y_1003_ = v___x_1021_;
v___y_1004_ = v___x_1026_;
goto v___jp_1001_;
}
else
{
v___y_1002_ = v___x_1020_;
v___y_1003_ = v___x_1021_;
v___y_1004_ = v___x_1024_;
goto v___jp_1001_;
}
}
else
{
v___y_1002_ = v___x_1020_;
v___y_1003_ = v___x_1021_;
v___y_1004_ = v___x_1022_;
goto v___jp_1001_;
}
}
else
{
return v___y_1015_;
}
}
v___jp_1027_:
{
if (lean_obj_tag(v___y_1028_) == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref_known(v___y_1028_, 1);
v___x_1029_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1030_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1031_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1033_ = l_Lean_Parser_registerAlias(v___x_1029_, v___x_1030_, v___x_1031_, v___x_1032_, v___x_857_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref_known(v___x_1033_, 1);
v___x_1034_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1035_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_1029_, v___x_1034_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1035_, 1);
v___x_1036_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1037_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_1029_, v___x_1036_);
v___y_1015_ = v___x_1037_;
goto v___jp_1014_;
}
else
{
v___y_1015_ = v___x_1035_;
goto v___jp_1014_;
}
}
else
{
v___y_1015_ = v___x_1033_;
goto v___jp_1014_;
}
}
else
{
return v___y_1028_;
}
}
v___jp_1038_:
{
if (lean_obj_tag(v___y_1039_) == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref_known(v___y_1039_, 1);
v___x_1040_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1041_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1042_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1043_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1044_ = l_Lean_Parser_registerAlias(v___x_1040_, v___x_1041_, v___x_1042_, v___x_1043_, v___x_857_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref_known(v___x_1044_, 1);
v___x_1045_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1046_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_1040_, v___x_1045_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref_known(v___x_1046_, 1);
v___x_1047_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_1048_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_1040_, v___x_1047_);
v___y_1028_ = v___x_1048_;
goto v___jp_1027_;
}
else
{
v___y_1028_ = v___x_1046_;
goto v___jp_1027_;
}
}
else
{
v___y_1028_ = v___x_1044_;
goto v___jp_1027_;
}
}
else
{
return v___y_1039_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1054_;
v_res_1054_ = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
return v_res_1056_;
}
}
lean_object* lean_mk_antiquot_parenthesizer(lean_object* v_name_1057_, lean_object* v_kind_1058_, uint8_t v_anonymous_1059_, uint8_t v_isPseudoKind_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Parser_mkAntiquot_parenthesizer(v_name_1057_, v_kind_1058_, v_anonymous_1059_, v_isPseudoKind_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v___x_1066_;
}
}
LEAN_EXPORT void lean_mk_antiquot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1057_ = stack[0].m_obj;
lean_object* v_kind_1058_ = stack[1].m_obj;
uint8_t v_anonymous_1059_ = stack[2].m_num;
uint8_t v_isPseudoKind_1060_ = stack[3].m_num;
lean_object* v_a_1061_ = stack[4].m_obj;
lean_object* v_a_1062_ = stack[5].m_obj;
lean_object* v_a_1063_ = stack[6].m_obj;
lean_object* v_a_1064_ = stack[7].m_obj;
lean_object* v_res_1067_;
v_res_1067_ = lean_mk_antiquot_parenthesizer(v_name_1057_, v_kind_1058_, v_anonymous_1059_, v_isPseudoKind_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object* v_name_1068_, lean_object* v_kind_1069_, lean_object* v_anonymous_1070_, lean_object* v_isPseudoKind_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
uint8_t v_anonymous_boxed_1077_; uint8_t v_isPseudoKind_boxed_1078_; lean_object* v_res_1079_; 
v_anonymous_boxed_1077_ = lean_unbox(v_anonymous_1070_);
v_isPseudoKind_boxed_1078_ = lean_unbox(v_isPseudoKind_1071_);
v_res_1079_ = lean_mk_antiquot_parenthesizer(v_name_1068_, v_kind_1069_, v_anonymous_boxed_1077_, v_isPseudoKind_boxed_1078_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v_res_1079_;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Parser_Term_ident_parenthesizer(v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1080_ = stack[0].m_obj;
lean_object* v_a_1081_ = stack[1].m_obj;
lean_object* v_a_1082_ = stack[2].m_obj;
lean_object* v_a_1083_ = stack[3].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___boxed(lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1092_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1(){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___f_1104_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0));
v___x_1105_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1106_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1107_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4));
v___x_1108_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1105_, v___x_1106_, v___x_1107_, v___f_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1109_;
v_res_1109_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___boxed(lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
return v_res_1111_;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Parser_Term_num_parenthesizer(v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1112_ = stack[0].m_obj;
lean_object* v_a_1113_ = stack[1].m_obj;
lean_object* v_a_1114_ = stack[2].m_obj;
lean_object* v_a_1115_ = stack[3].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___boxed(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___f_1133_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0));
v___x_1134_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1135_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1136_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1));
v___x_1137_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1134_, v___x_1135_, v___x_1136_, v___f_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1138_;
v_res_1138_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___boxed(lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
return v_res_1140_;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Parser_Term_scientific_parenthesizer(v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1141_ = stack[0].m_obj;
lean_object* v_a_1142_ = stack[1].m_obj;
lean_object* v_a_1143_ = stack[2].m_obj;
lean_object* v_a_1144_ = stack[3].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___boxed(lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1153_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___f_1162_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0));
v___x_1163_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1164_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1165_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1));
v___x_1166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1163_, v___x_1164_, v___x_1165_, v___f_1162_);
return v___x_1166_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1167_;
v_res_1167_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___boxed(lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
return v_res_1169_;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Parser_Term_char_parenthesizer(v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1170_ = stack[0].m_obj;
lean_object* v_a_1171_ = stack[1].m_obj;
lean_object* v_a_1172_ = stack[2].m_obj;
lean_object* v_a_1173_ = stack[3].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___boxed(lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1182_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___f_1191_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0));
v___x_1192_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1193_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1194_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1));
v___x_1195_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1192_, v___x_1193_, v___x_1194_, v___f_1191_);
return v___x_1195_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1196_;
v_res_1196_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
stack->m_obj
 = v_res_1196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___boxed(lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
return v_res_1198_;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Parser_Term_str_parenthesizer(v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1199_ = stack[0].m_obj;
lean_object* v_a_1200_ = stack[1].m_obj;
lean_object* v_a_1201_ = stack[2].m_obj;
lean_object* v_a_1202_ = stack[3].m_obj;
lean_object* v_res_1205_;
v_res_1205_ = l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___boxed(lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1211_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___f_1220_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0));
v___x_1221_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1222_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1223_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1));
v___x_1224_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1221_, v___x_1222_, v___x_1223_, v___f_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1225_;
v_res_1225_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
stack->m_obj
 = v_res_1225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___boxed(lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
return v_res_1227_;
}
}
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object* v_x_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
switch(lean_obj_tag(v_x_1228_))
{
case 0:
{
lean_object* v_name_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1230_);
v_name_1232_ = lean_ctor_get(v_x_1228_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1234_ = v_x_1228_;
v_isShared_1235_ = v_isSharedCheck_1261_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_name_1232_);
lean_dec(v_x_1228_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1261_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_ref_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_ref_1236_ = lean_ctor_get(v_a_1229_, 2);
lean_inc(v_ref_1236_);
lean_dec_ref(v_a_1229_);
v___x_1237_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1238_ = l_Lean_Parser_getConstAlias___redArg(v___x_1237_, v_name_1232_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_ref_1236_);
lean_del_object(v___x_1234_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1260_; 
v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1249_ = v___x_1238_;
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1238_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_io_error_to_string(v_a_1247_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set_tag(v___x_1234_, 3);
lean_ctor_set(v___x_1234_, 0, v___x_1251_);
v___x_1253_ = v___x_1234_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = l_Lean_MessageData_ofFormat(v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_ref_1236_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1255_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
case 1:
{
lean_object* v_name_1262_; lean_object* v_p_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1295_; 
v_name_1262_ = lean_ctor_get(v_x_1228_, 0);
v_p_1263_ = lean_ctor_get(v_x_1228_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1265_ = v_x_1228_;
v_isShared_1266_ = v_isSharedCheck_1295_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_p_1263_);
lean_inc(v_name_1262_);
lean_dec(v_x_1228_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1295_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_ref_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_ref_1267_ = lean_ctor_get(v_a_1229_, 2);
v___x_1268_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1269_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1268_, v_name_1262_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
lean_del_object(v___x_1265_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1263_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_apply_1(v_a_1270_, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_dec(v_a_1270_);
return v___x_1271_;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1294_; 
lean_inc(v_ref_1267_);
lean_dec_ref(v_p_1263_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_a_1281_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1283_ = v___x_1269_;
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1269_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1285_ = lean_io_error_to_string(v_a_1281_);
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = l_Lean_MessageData_ofFormat(v___x_1286_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 0);
lean_ctor_set(v___x_1265_, 1, v___x_1287_);
lean_ctor_set(v___x_1265_, 0, v_ref_1267_);
v___x_1289_ = v___x_1265_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_ref_1267_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1289_);
v___x_1291_ = v___x_1283_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
case 2:
{
lean_object* v_name_1296_; lean_object* v_p_u2081_1297_; lean_object* v_p_u2082_1298_; lean_object* v_ref_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_name_1296_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_name_1296_);
v_p_u2081_1297_ = lean_ctor_get(v_x_1228_, 1);
lean_inc_ref(v_p_u2081_1297_);
v_p_u2082_1298_ = lean_ctor_get(v_x_1228_, 2);
lean_inc_ref(v_p_u2082_1298_);
lean_dec_ref_known(v_x_1228_, 3);
v_ref_1299_ = lean_ctor_get(v_a_1229_, 2);
v___x_1300_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1301_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1300_, v_name_1296_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
lean_inc(v_a_1230_);
lean_inc_ref(v_a_1229_);
v___x_1303_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_u2081_1297_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_u2082_1298_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1314_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_apply_2(v_a_1302_, v_a_1304_, v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1310_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_dec(v_a_1304_);
lean_dec(v_a_1302_);
return v___x_1305_;
}
}
else
{
lean_dec(v_a_1302_);
lean_dec_ref(v_p_u2082_1298_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1303_;
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
lean_inc(v_ref_1299_);
lean_dec_ref(v_p_u2082_1298_);
lean_dec_ref(v_p_u2081_1297_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_a_1315_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1317_ = v___x_1301_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1301_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1319_ = lean_io_error_to_string(v_a_1315_);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = l_Lean_MessageData_ofFormat(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_ref_1299_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
case 3:
{
lean_object* v_kind_1327_; lean_object* v_prec_1328_; lean_object* v_p_1329_; lean_object* v___x_1330_; 
v_kind_1327_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_kind_1327_);
v_prec_1328_ = lean_ctor_get(v_x_1228_, 1);
lean_inc(v_prec_1328_);
v_p_1329_ = lean_ctor_get(v_x_1228_, 2);
lean_inc_ref(v_p_1329_);
lean_dec_ref_known(v_x_1228_, 3);
v___x_1330_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1329_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1335_, 0, v_kind_1327_);
lean_closure_set(v___x_1335_, 1, v_prec_1328_);
lean_closure_set(v___x_1335_, 2, v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_dec(v_prec_1328_);
lean_dec(v_kind_1327_);
return v___x_1330_;
}
}
case 4:
{
lean_object* v_kind_1340_; lean_object* v_prec_1341_; lean_object* v_lhsPrec_1342_; lean_object* v_p_1343_; lean_object* v___x_1344_; 
v_kind_1340_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_kind_1340_);
v_prec_1341_ = lean_ctor_get(v_x_1228_, 1);
lean_inc(v_prec_1341_);
v_lhsPrec_1342_ = lean_ctor_get(v_x_1228_, 2);
lean_inc(v_lhsPrec_1342_);
v_p_1343_ = lean_ctor_get(v_x_1228_, 3);
lean_inc_ref(v_p_1343_);
lean_dec_ref_known(v_x_1228_, 4);
v___x_1344_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1343_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1349_, 0, v_kind_1340_);
lean_closure_set(v___x_1349_, 1, v_prec_1341_);
lean_closure_set(v___x_1349_, 2, v_lhsPrec_1342_);
lean_closure_set(v___x_1349_, 3, v_a_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_dec(v_lhsPrec_1342_);
lean_dec(v_prec_1341_);
lean_dec(v_kind_1340_);
return v___x_1344_;
}
}
case 5:
{
lean_object* v_val_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_val_1354_ = lean_ctor_get(v_x_1228_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1356_ = v_x_1228_;
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_val_1354_);
lean_dec(v_x_1228_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1358_, 0, v_val_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
case 6:
{
lean_object* v_val_1363_; uint8_t v_includeIdent_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_val_1363_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_val_1363_);
v_includeIdent_1364_ = lean_ctor_get_uint8(v_x_1228_, sizeof(void*)*1);
lean_dec_ref_known(v_x_1228_, 1);
v___x_1365_ = lean_box(v_includeIdent_1364_);
v___x_1366_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1366_, 0, v_val_1363_);
lean_closure_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
case 7:
{
lean_object* v_catName_1368_; lean_object* v_rbp_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_catName_1368_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_catName_1368_);
v_rbp_1369_ = lean_ctor_get(v_x_1228_, 1);
lean_inc(v_rbp_1369_);
lean_dec_ref_known(v_x_1228_, 2);
v___x_1370_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1370_, 0, v_catName_1368_);
lean_closure_set(v___x_1370_, 1, v_rbp_1369_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
case 8:
{
lean_object* v_declName_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_declName_1372_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_declName_1372_);
lean_dec_ref_known(v_x_1228_, 1);
v___x_1373_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
v___x_1374_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v___x_1373_, v_declName_1372_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1374_;
}
case 9:
{
lean_object* v_name_1375_; lean_object* v_kind_1376_; lean_object* v_p_1377_; lean_object* v___x_1378_; 
v_name_1375_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_name_1375_);
v_kind_1376_ = lean_ctor_get(v_x_1228_, 1);
lean_inc(v_kind_1376_);
v_p_1377_ = lean_ctor_get(v_x_1228_, 2);
lean_inc_ref(v_p_1377_);
lean_dec_ref_known(v_x_1228_, 3);
v___x_1378_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1377_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1393_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1393_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1393_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1383_ = 1;
v___x_1384_ = 0;
v___x_1385_ = lean_box(v___x_1383_);
v___x_1386_ = lean_box(v___x_1384_);
lean_inc(v_kind_1376_);
v___x_1387_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 9, 4);
lean_closure_set(v___x_1387_, 0, v_name_1375_);
lean_closure_set(v___x_1387_, 1, v_kind_1376_);
lean_closure_set(v___x_1387_, 2, v___x_1385_);
lean_closure_set(v___x_1387_, 3, v___x_1386_);
v___x_1388_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1388_, 0, v_kind_1376_);
lean_closure_set(v___x_1388_, 1, v_a_1379_);
v___x_1389_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1389_, 0, v___x_1387_);
lean_closure_set(v___x_1389_, 1, v___x_1388_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1389_);
v___x_1391_ = v___x_1381_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_dec(v_kind_1376_);
lean_dec_ref(v_name_1375_);
return v___x_1378_;
}
}
case 10:
{
lean_object* v_p_1394_; lean_object* v_sep_1395_; lean_object* v_psep_1396_; uint8_t v_allowTrailingSep_1397_; lean_object* v___x_1398_; 
v_p_1394_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_p_1394_);
v_sep_1395_ = lean_ctor_get(v_x_1228_, 1);
lean_inc_ref(v_sep_1395_);
v_psep_1396_ = lean_ctor_get(v_x_1228_, 2);
lean_inc_ref(v_psep_1396_);
v_allowTrailingSep_1397_ = lean_ctor_get_uint8(v_x_1228_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1228_, 3);
lean_inc(v_a_1230_);
lean_inc_ref(v_a_1229_);
v___x_1398_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1394_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_psep_1396_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_box(v_allowTrailingSep_1397_);
v___x_1406_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1406_, 0, v_a_1399_);
lean_closure_set(v___x_1406_, 1, v_sep_1395_);
lean_closure_set(v___x_1406_, 2, v_a_1401_);
lean_closure_set(v___x_1406_, 3, v___x_1405_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref(v_sep_1395_);
return v___x_1400_;
}
}
else
{
lean_dec_ref(v_psep_1396_);
lean_dec_ref(v_sep_1395_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1398_;
}
}
case 11:
{
lean_object* v_p_1411_; lean_object* v_sep_1412_; lean_object* v_psep_1413_; uint8_t v_allowTrailingSep_1414_; lean_object* v___x_1415_; 
v_p_1411_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_p_1411_);
v_sep_1412_ = lean_ctor_get(v_x_1228_, 1);
lean_inc_ref(v_sep_1412_);
v_psep_1413_ = lean_ctor_get(v_x_1228_, 2);
lean_inc_ref(v_psep_1413_);
v_allowTrailingSep_1414_ = lean_ctor_get_uint8(v_x_1228_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1228_, 3);
lean_inc(v_a_1230_);
lean_inc_ref(v_a_1229_);
v___x_1415_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1411_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_psep_1413_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1427_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1427_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1427_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = lean_box(v_allowTrailingSep_1414_);
v___x_1423_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1423_, 0, v_a_1416_);
lean_closure_set(v___x_1423_, 1, v_sep_1412_);
lean_closure_set(v___x_1423_, 2, v_a_1418_);
lean_closure_set(v___x_1423_, 3, v___x_1422_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_dec(v_a_1416_);
lean_dec_ref(v_sep_1412_);
return v___x_1417_;
}
}
else
{
lean_dec_ref(v_psep_1413_);
lean_dec_ref(v_sep_1412_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1415_;
}
}
default: 
{
lean_object* v_val_1428_; lean_object* v_asciiVal_1429_; uint8_t v_preserveForPP_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
v_val_1428_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_val_1428_);
v_asciiVal_1429_ = lean_ctor_get(v_x_1228_, 1);
lean_inc_ref(v_asciiVal_1429_);
v_preserveForPP_1430_ = lean_ctor_get_uint8(v_x_1228_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1228_, 2);
v___x_1431_ = lean_box(v_preserveForPP_1430_);
v___x_1432_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbol_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1432_, 0, v_val_1428_);
lean_closure_set(v___x_1432_, 1, v_asciiVal_1429_);
lean_closure_set(v___x_1432_, 2, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT void lean_pretty_printer_parenthesizer_interpret_parser_descr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1228_ = stack[0].m_obj;
lean_object* v_a_1229_ = stack[1].m_obj;
lean_object* v_a_1230_ = stack[2].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_x_1228_, v_a_1229_, v_a_1230_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___boxed(lean_object* v_x_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_x_1435_, v_a_1436_, v_a_1437_);
return v_res_1439_;
}
}
lean_object* lean_mk_antiquot_formatter(lean_object* v_name_1440_, lean_object* v_kind_1441_, uint8_t v_anonymous_1442_, uint8_t v_isPseudoKind_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Parser_mkAntiquot_formatter(v_name_1440_, v_kind_1441_, v_anonymous_1442_, v_isPseudoKind_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v___x_1449_;
}
}
LEAN_EXPORT void lean_mk_antiquot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1440_ = stack[0].m_obj;
lean_object* v_kind_1441_ = stack[1].m_obj;
uint8_t v_anonymous_1442_ = stack[2].m_num;
uint8_t v_isPseudoKind_1443_ = stack[3].m_num;
lean_object* v_a_1444_ = stack[4].m_obj;
lean_object* v_a_1445_ = stack[5].m_obj;
lean_object* v_a_1446_ = stack[6].m_obj;
lean_object* v_a_1447_ = stack[7].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = lean_mk_antiquot_formatter(v_name_1440_, v_kind_1441_, v_anonymous_1442_, v_isPseudoKind_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object* v_name_1451_, lean_object* v_kind_1452_, lean_object* v_anonymous_1453_, lean_object* v_isPseudoKind_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
uint8_t v_anonymous_boxed_1460_; uint8_t v_isPseudoKind_boxed_1461_; lean_object* v_res_1462_; 
v_anonymous_boxed_1460_ = lean_unbox(v_anonymous_1453_);
v_isPseudoKind_boxed_1461_ = lean_unbox(v_isPseudoKind_1454_);
v_res_1462_ = lean_mk_antiquot_formatter(v_name_1451_, v_kind_1452_, v_anonymous_boxed_1460_, v_isPseudoKind_boxed_1461_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
return v_res_1462_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Parser_Term_ident_formatter(v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_ident_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1463_ = stack[0].m_obj;
lean_object* v_a_1464_ = stack[1].m_obj;
lean_object* v_a_1465_ = stack[2].m_obj;
lean_object* v_a_1466_ = stack[3].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_PrettyPrinter_Formatter_ident_formatter(v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter___boxed(lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_PrettyPrinter_Formatter_ident_formatter(v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1475_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1(){
_start:
{
lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___f_1486_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0));
v___x_1487_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1488_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1489_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3));
v___x_1490_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1487_, v___x_1488_, v___x_1489_, v___f_1486_);
return v___x_1490_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1491_;
v_res_1491_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
stack->m_obj
 = v_res_1491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___boxed(lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
return v_res_1493_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Parser_Term_num_formatter(v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_numLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1494_ = stack[0].m_obj;
lean_object* v_a_1495_ = stack[1].m_obj;
lean_object* v_a_1496_ = stack[2].m_obj;
lean_object* v_a_1497_ = stack[3].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_Lean_PrettyPrinter_Formatter_numLit_formatter(v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter___boxed(lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_PrettyPrinter_Formatter_numLit_formatter(v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1506_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1(){
_start:
{
lean_object* v___f_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___f_1515_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0));
v___x_1516_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1517_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1518_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1));
v___x_1519_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1516_, v___x_1517_, v___x_1518_, v___f_1515_);
return v___x_1519_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1520_;
v_res_1520_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
stack->m_obj
 = v_res_1520_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___boxed(lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
return v_res_1522_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Parser_Term_scientific_formatter(v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_scientificLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1523_ = stack[0].m_obj;
lean_object* v_a_1524_ = stack[1].m_obj;
lean_object* v_a_1525_ = stack[2].m_obj;
lean_object* v_a_1526_ = stack[3].m_obj;
lean_object* v_res_1529_;
v_res_1529_ = l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
stack->m_obj
 = v_res_1529_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter___boxed(lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1535_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1(){
_start:
{
lean_object* v___f_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___f_1544_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0));
v___x_1545_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1546_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1547_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1));
v___x_1548_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1545_, v___x_1546_, v___x_1547_, v___f_1544_);
return v___x_1548_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1549_;
v_res_1549_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
stack->m_obj
 = v_res_1549_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___boxed(lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
return v_res_1551_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Parser_Term_char_formatter(v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_charLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1552_ = stack[0].m_obj;
lean_object* v_a_1553_ = stack[1].m_obj;
lean_object* v_a_1554_ = stack[2].m_obj;
lean_object* v_a_1555_ = stack[3].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l_Lean_PrettyPrinter_Formatter_charLit_formatter(v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter___boxed(lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_PrettyPrinter_Formatter_charLit_formatter(v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1564_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1(){
_start:
{
lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___f_1573_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0));
v___x_1574_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1575_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1576_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1));
v___x_1577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1574_, v___x_1575_, v___x_1576_, v___f_1573_);
return v___x_1577_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1578_;
v_res_1578_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___boxed(lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
return v_res_1580_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Parser_Term_str_formatter(v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_strLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1581_ = stack[0].m_obj;
lean_object* v_a_1582_ = stack[1].m_obj;
lean_object* v_a_1583_ = stack[2].m_obj;
lean_object* v_a_1584_ = stack[3].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_PrettyPrinter_Formatter_strLit_formatter(v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter___boxed(lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_PrettyPrinter_Formatter_strLit_formatter(v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1593_;
}
}
lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1(){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___f_1602_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0));
v___x_1603_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1604_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1605_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1));
v___x_1606_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1603_, v___x_1604_, v___x_1605_, v___f_1602_);
return v___x_1606_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1607_;
v_res_1607_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___boxed(lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
return v_res_1609_;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1610_, v___x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1610_ = stack[0].m_obj;
lean_object* v___x_1611_ = stack[1].m_obj;
lean_object* v___y_1612_ = stack[2].m_obj;
lean_object* v___y_1613_ = stack[3].m_obj;
lean_object* v___y_1614_ = stack[4].m_obj;
lean_object* v___y_1615_ = stack[5].m_obj;
lean_object* v_res_1618_;
v_res_1618_ = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(v___x_1610_, v___x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
stack->m_obj
 = v_res_1618_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed(lean_object* v___x_1619_, lean_object* v___x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(v___x_1619_, v___x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1626_;
}
}
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* v_x_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
switch(lean_obj_tag(v_x_1627_))
{
case 0:
{
lean_object* v_name_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1629_);
v_name_1631_ = lean_ctor_get(v_x_1627_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1633_ = v_x_1627_;
v_isShared_1634_ = v_isSharedCheck_1660_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_name_1631_);
lean_dec(v_x_1627_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1660_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v_ref_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_ref_1635_ = lean_ctor_get(v_a_1628_, 2);
lean_inc(v_ref_1635_);
lean_dec_ref(v_a_1628_);
v___x_1636_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1637_ = l_Lean_Parser_getConstAlias___redArg(v___x_1636_, v_name_1631_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_ref_1635_);
lean_del_object(v___x_1633_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1659_; 
v_a_1646_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1648_ = v___x_1637_;
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1637_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_io_error_to_string(v_a_1646_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 3);
lean_ctor_set(v___x_1633_, 0, v___x_1650_);
v___x_1652_ = v___x_1633_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = l_Lean_MessageData_ofFormat(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_ref_1635_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1654_);
v___x_1656_ = v___x_1648_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
case 1:
{
lean_object* v_name_1661_; lean_object* v_p_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1694_; 
v_name_1661_ = lean_ctor_get(v_x_1627_, 0);
v_p_1662_ = lean_ctor_get(v_x_1627_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1664_ = v_x_1627_;
v_isShared_1665_ = v_isSharedCheck_1694_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_p_1662_);
lean_inc(v_name_1661_);
lean_dec(v_x_1627_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1694_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_ref_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_ref_1666_ = lean_ctor_get(v_a_1628_, 2);
v___x_1667_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1668_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1667_, v_name_1661_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
lean_del_object(v___x_1664_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1662_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1679_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_apply_1(v_a_1669_, v_a_1671_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_dec(v_a_1669_);
return v___x_1670_;
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1693_; 
lean_inc(v_ref_1666_);
lean_dec_ref(v_p_1662_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_a_1680_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1682_ = v___x_1668_;
v_isShared_1683_ = v_isSharedCheck_1693_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1668_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1693_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1684_ = lean_io_error_to_string(v_a_1680_);
v___x_1685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___x_1686_ = l_Lean_MessageData_ofFormat(v___x_1685_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 0);
lean_ctor_set(v___x_1664_, 1, v___x_1686_);
lean_ctor_set(v___x_1664_, 0, v_ref_1666_);
v___x_1688_ = v___x_1664_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_ref_1666_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1688_);
v___x_1690_ = v___x_1682_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
case 2:
{
lean_object* v_name_1695_; lean_object* v_p_u2081_1696_; lean_object* v_p_u2082_1697_; lean_object* v_ref_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_name_1695_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_name_1695_);
v_p_u2081_1696_ = lean_ctor_get(v_x_1627_, 1);
lean_inc_ref(v_p_u2081_1696_);
v_p_u2082_1697_ = lean_ctor_get(v_x_1627_, 2);
lean_inc_ref(v_p_u2082_1697_);
lean_dec_ref_known(v_x_1627_, 3);
v_ref_1698_ = lean_ctor_get(v_a_1628_, 2);
v___x_1699_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1700_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1699_, v_name_1695_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
lean_inc(v_a_1629_);
lean_inc_ref(v_a_1628_);
v___x_1702_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_u2081_1696_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_u2082_1697_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_apply_2(v_a_1701_, v_a_1703_, v_a_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_dec(v_a_1703_);
lean_dec(v_a_1701_);
return v___x_1704_;
}
}
else
{
lean_dec(v_a_1701_);
lean_dec_ref(v_p_u2082_1697_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v___x_1702_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1725_; 
lean_inc(v_ref_1698_);
lean_dec_ref(v_p_u2082_1697_);
lean_dec_ref(v_p_u2081_1696_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_a_1714_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1716_ = v___x_1700_;
v_isShared_1717_ = v_isSharedCheck_1725_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1700_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1725_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1718_ = lean_io_error_to_string(v_a_1714_);
v___x_1719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___x_1720_ = l_Lean_MessageData_ofFormat(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_ref_1698_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1721_);
v___x_1723_ = v___x_1716_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
case 3:
{
lean_object* v_kind_1726_; lean_object* v_p_1727_; lean_object* v___x_1728_; 
v_kind_1726_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_kind_1726_);
v_p_1727_ = lean_ctor_get(v_x_1627_, 2);
lean_inc_ref(v_p_1727_);
lean_dec_ref_known(v_x_1627_, 3);
v___x_1728_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1727_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_1733_, 0, v_kind_1726_);
lean_closure_set(v___x_1733_, 1, v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_dec(v_kind_1726_);
return v___x_1728_;
}
}
case 4:
{
lean_object* v_kind_1738_; lean_object* v_prec_1739_; lean_object* v_lhsPrec_1740_; lean_object* v_p_1741_; lean_object* v___x_1742_; 
v_kind_1738_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_kind_1738_);
v_prec_1739_ = lean_ctor_get(v_x_1627_, 1);
lean_inc(v_prec_1739_);
v_lhsPrec_1740_ = lean_ctor_get(v_x_1627_, 2);
lean_inc(v_lhsPrec_1740_);
v_p_1741_ = lean_ctor_get(v_x_1627_, 3);
lean_inc_ref(v_p_1741_);
lean_dec_ref_known(v_x_1627_, 4);
v___x_1742_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1741_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed), 9, 4);
lean_closure_set(v___x_1747_, 0, v_kind_1738_);
lean_closure_set(v___x_1747_, 1, v_prec_1739_);
lean_closure_set(v___x_1747_, 2, v_lhsPrec_1740_);
lean_closure_set(v___x_1747_, 3, v_a_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_dec(v_lhsPrec_1740_);
lean_dec(v_prec_1739_);
lean_dec(v_kind_1738_);
return v___x_1742_;
}
}
case 5:
{
lean_object* v_val_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_val_1752_ = lean_ctor_get(v_x_1627_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1754_ = v_x_1627_;
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_val_1752_);
lean_dec(v_x_1627_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter___boxed), 6, 1);
lean_closure_set(v___x_1756_, 0, v_val_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
case 6:
{
lean_object* v_val_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_val_1761_ = lean_ctor_get(v_x_1627_, 0);
lean_inc_ref(v_val_1761_);
lean_dec_ref_known(v_x_1627_, 1);
v___x_1762_ = 0;
v___x_1763_ = lean_box(v___x_1762_);
v___x_1764_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(v___x_1764_, 0, v_val_1761_);
lean_closure_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
case 7:
{
lean_object* v_catName_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_catName_1766_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_catName_1766_);
lean_dec_ref_known(v_x_1627_, 2);
v___x_1767_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed), 6, 1);
lean_closure_set(v___x_1767_, 0, v_catName_1766_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
case 8:
{
lean_object* v_declName_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_declName_1769_ = lean_ctor_get(v_x_1627_, 0);
lean_inc(v_declName_1769_);
lean_dec_ref_known(v_x_1627_, 1);
v___x_1770_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
v___x_1771_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v___x_1770_, v_declName_1769_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v___x_1771_;
}
case 9:
{
lean_object* v_name_1772_; lean_object* v_kind_1773_; lean_object* v_p_1774_; lean_object* v___x_1775_; 
v_name_1772_ = lean_ctor_get(v_x_1627_, 0);
lean_inc_ref(v_name_1772_);
v_kind_1773_ = lean_ctor_get(v_x_1627_, 1);
lean_inc(v_kind_1773_);
v_p_1774_ = lean_ctor_get(v_x_1627_, 2);
lean_inc_ref(v_p_1774_);
lean_dec_ref_known(v_x_1627_, 3);
v___x_1775_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1774_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1790_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
uint8_t v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___f_1786_; lean_object* v___x_1788_; 
v___x_1780_ = 1;
v___x_1781_ = 0;
v___x_1782_ = lean_box(v___x_1780_);
v___x_1783_ = lean_box(v___x_1781_);
lean_inc(v_kind_1773_);
v___x_1784_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(v___x_1784_, 0, v_name_1772_);
lean_closure_set(v___x_1784_, 1, v_kind_1773_);
lean_closure_set(v___x_1784_, 2, v___x_1782_);
lean_closure_set(v___x_1784_, 3, v___x_1783_);
v___x_1785_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_1785_, 0, v_kind_1773_);
lean_closure_set(v___x_1785_, 1, v_a_1776_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1786_, 0, v___x_1784_);
lean_closure_set(v___f_1786_, 1, v___x_1785_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___f_1786_);
v___x_1788_ = v___x_1778_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___f_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_dec(v_kind_1773_);
lean_dec_ref(v_name_1772_);
return v___x_1775_;
}
}
case 10:
{
lean_object* v_p_1791_; lean_object* v_sep_1792_; lean_object* v_psep_1793_; uint8_t v_allowTrailingSep_1794_; lean_object* v___x_1795_; 
v_p_1791_ = lean_ctor_get(v_x_1627_, 0);
lean_inc_ref(v_p_1791_);
v_sep_1792_ = lean_ctor_get(v_x_1627_, 1);
lean_inc_ref(v_sep_1792_);
v_psep_1793_ = lean_ctor_get(v_x_1627_, 2);
lean_inc_ref(v_psep_1793_);
v_allowTrailingSep_1794_ = lean_ctor_get_uint8(v_x_1627_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1627_, 3);
lean_inc(v_a_1629_);
lean_inc_ref(v_a_1628_);
v___x_1795_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1791_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = lean_pretty_printer_formatter_interpret_parser_descr(v_psep_1793_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1807_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = lean_box(v_allowTrailingSep_1794_);
v___x_1803_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_formatter___boxed), 9, 4);
lean_closure_set(v___x_1803_, 0, v_a_1796_);
lean_closure_set(v___x_1803_, 1, v_sep_1792_);
lean_closure_set(v___x_1803_, 2, v_a_1798_);
lean_closure_set(v___x_1803_, 3, v___x_1802_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_dec(v_a_1796_);
lean_dec_ref(v_sep_1792_);
return v___x_1797_;
}
}
else
{
lean_dec_ref(v_psep_1793_);
lean_dec_ref(v_sep_1792_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v___x_1795_;
}
}
case 11:
{
lean_object* v_p_1808_; lean_object* v_sep_1809_; lean_object* v_psep_1810_; uint8_t v_allowTrailingSep_1811_; lean_object* v___x_1812_; 
v_p_1808_ = lean_ctor_get(v_x_1627_, 0);
lean_inc_ref(v_p_1808_);
v_sep_1809_ = lean_ctor_get(v_x_1627_, 1);
lean_inc_ref(v_sep_1809_);
v_psep_1810_ = lean_ctor_get(v_x_1627_, 2);
lean_inc_ref(v_psep_1810_);
v_allowTrailingSep_1811_ = lean_ctor_get_uint8(v_x_1627_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1627_, 3);
lean_inc(v_a_1629_);
lean_inc_ref(v_a_1628_);
v___x_1812_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1808_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = lean_pretty_printer_formatter_interpret_parser_descr(v_psep_1810_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_box(v_allowTrailingSep_1811_);
v___x_1820_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_1820_, 0, v_a_1813_);
lean_closure_set(v___x_1820_, 1, v_sep_1809_);
lean_closure_set(v___x_1820_, 2, v_a_1815_);
lean_closure_set(v___x_1820_, 3, v___x_1819_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_dec(v_a_1813_);
lean_dec_ref(v_sep_1809_);
return v___x_1814_;
}
}
else
{
lean_dec_ref(v_psep_1810_);
lean_dec_ref(v_sep_1809_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v___x_1812_;
}
}
default: 
{
lean_object* v_val_1825_; lean_object* v_asciiVal_1826_; uint8_t v_preserveForPP_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
v_val_1825_ = lean_ctor_get(v_x_1627_, 0);
lean_inc_ref(v_val_1825_);
v_asciiVal_1826_ = lean_ctor_get(v_x_1627_, 1);
lean_inc_ref(v_asciiVal_1826_);
v_preserveForPP_1827_ = lean_ctor_get_uint8(v_x_1627_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1627_, 2);
v___x_1828_ = lean_box(v_preserveForPP_1827_);
v___x_1829_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_1829_, 0, v_val_1825_);
lean_closure_set(v___x_1829_, 1, v_asciiVal_1826_);
lean_closure_set(v___x_1829_, 2, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
}
}
LEAN_EXPORT void lean_pretty_printer_formatter_interpret_parser_descr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1627_ = stack[0].m_obj;
lean_object* v_a_1628_ = stack[1].m_obj;
lean_object* v_a_1629_ = stack[2].m_obj;
lean_object* v_res_1831_;
v_res_1831_ = lean_pretty_printer_formatter_interpret_parser_descr(v_x_1627_, v_a_1628_, v_a_1629_);
stack->m_obj
 = v_res_1831_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___boxed(lean_object* v_x_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = lean_pretty_printer_formatter_interpret_parser_descr(v_x_1832_, v_a_1833_, v_a_1834_);
return v_res_1836_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
