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
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_Term_str_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookahead(lean_object*);
lean_object* l_Lean_Parser_Term_str_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_Term_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_scientificLit;
lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hygieneInfo;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
extern lean_object* l_Lean_Parser_rawIdent;
lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLineEq(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hexnum;
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_Term_scientific_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 198, 251, 95, 67, 81, 118, 246)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "checkWsBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 180, 243, 53, 77, 82, 55, 205)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "space before"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkNoWsBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 175, 148, 38, 136, 238, 167, 124)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 147, 100, 44, 136, 108, 159, 66)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "checkLinebreakBefore"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 136, 117, 184, 203, 101, 193, 45)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "numLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 124, 25, 195, 9, 201, 171, 221)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 157, 94, 66, 135, 29, 115, 44)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "charLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 82, 20, 217, 44, 105, 253, 153)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_charLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_charLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nameLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 229, 203, 158, 195, 74, 86, 122)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nameLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nameLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "scientificLit"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 25, 249, 160, 8, 56, 13, 159)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_scientificLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_scientificLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 242, 101, 31, 193, 156, 127, 171)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rawIdent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 100, 176, 236, 81, 164, 232, 12)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 2, 179, 39, 67, 204, 226, 154)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 96, 174, 177, 221, 86, 223, 51)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_hygieneInfo_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_hygieneInfo_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGt"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 27, 6, 116, 51, 223, 220, 245)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGe"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 21, 222, 233, 68, 88, 239, 150)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 155, 248, 3, 115, 223, 12, 139)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 79, 136, 97, 27, 86, 56, 4)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lineEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 222, 52, 211, 142, 186, 26, 103)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkLineEq"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 130, 255, 142, 22, 38, 200, 197)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 94, 230, 204, 13, 59, 242, 46)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 19, 60, 201, 90, 143, 111, 211)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_lookahead, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 16, 254, 130, 153, 255, 99, 153)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 114, 232, 230, 181, 52, 168, 160)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 61, 196, 93, 201, 246, 193, 192)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "manyIndent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 35, 49, 198, 227, 245, 222, 169)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 71, 18, 147, 220, 40, 152, 21)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_manyIndent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_manyIndent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "many1Indent"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 232, 149, 52, 5, 17, 36, 232)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 214, 77, 50, 137, 69, 220, 172)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1Indent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1Indent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 167, 191, 130, 216, 220, 182, 40)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 188, 255, 221, 143, 31, 128, 82)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withPosition, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 222, 221, 61, 47, 46, 252, 242)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 202, 249, 244, 227, 198, 135, 34)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 23, 219, 174, 6, 42, 106, 219)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutForbidden_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 182, 82, 21, 251, 127, 209, 38)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_interpolatedStr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 234, 249, 199, 49, 244, 72, 166)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 70, 47, 117, 238, 126, 239, 49)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_orelse, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 226, 49, 74, 122, 217, 187, 147)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_andthen, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 177, 38, 2, 101, 67, 237, 158)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 137, 49, 69, 62, 133, 213, 34)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_recover, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "notFollowedBy"};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 55, 249, 172, 87, 126, 186, 81)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 0, 133, 48, 146, 73, 208, 113)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_0__Lean_Parser_initFn___closed__307_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___closed__307_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__307_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value;
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 233, 14, 51, 59, 26, 143, 93)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 160, 160, 165, 225, 137, 109, 89)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 169, 213, 135, 193, 195, 181, 162)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 21, 185, 140, 206, 31, 0, 27)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 61, 18, 10, 61, 249, 234, 173)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 7, 102, 176, 201, 50, 36, 151)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 145, 199, 126, 121, 58, 89, 39)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 39, 82, 251, 165, 33, 85, 105)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 247, 13, 105, 80, 134, 66, 66)}};
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
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 191, 21, 76, 153, 54, 88, 65)}};
static const lean_ctor_object l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 22, 145, 4, 145, 86, 25, 230)}};
static const lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_4_ = l_Lean_Parser_notFollowedBy(v_x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_6_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_11_, v___y_12_, v___y_13_, v___y_14_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_5(v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
return v_res_30_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_33_ = l_Lean_Parser_checkColGe(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_36_ = l_Lean_Parser_andthen(v___x_35_, v___y_34_);
v___x_37_ = l_Lean_Parser_many(v___x_36_);
v___x_38_ = l_Lean_Parser_withPosition(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_41_ = l_Lean_Parser_andthen(v___x_40_, v___y_39_);
v___x_42_ = l_Lean_Parser_many1(v___x_41_);
v___x_43_ = l_Lean_Parser_withPosition(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_45_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_apply_5(v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, lean_box(0));
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v_res_69_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_89_ = l_Lean_Parser_checkWsBefore(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed), 5, 0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed), 5, 0);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_114_ = l_Lean_Parser_checkNoWsBefore(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_133_ = l_Lean_Parser_checkLinebreakBefore(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Lean_Parser_numLit;
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lean_Parser_strLit;
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = l_Lean_Parser_charLit;
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Lean_Parser_nameLit;
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = l_Lean_Parser_scientificLit;
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = l_Lean_Parser_ident;
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = l_Lean_Parser_rawIdent;
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Lean_Parser_hygieneInfo;
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_296_ = l_Lean_Parser_checkColGt(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_314_ = l_Lean_Parser_checkColGe(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_332_ = l_Lean_Parser_checkColEq(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed), 5, 0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_350_ = l_Lean_Parser_checkLineEq(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_Parser_hexnum;
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed), 5, 0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_647_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_648_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_649_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_650_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_651_ = l_Lean_Parser_registerAlias(v___x_646_, v___x_647_, v___x_648_, v___x_649_, v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_653_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_646_, v___x_652_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref_known(v___x_653_, 1);
v___x_654_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_655_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_646_, v___x_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec_ref_known(v___x_655_, 1);
v___x_656_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_657_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_658_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_659_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_660_ = l_Lean_Parser_registerAlias(v___x_656_, v___x_657_, v___x_658_, v___x_659_, v___x_650_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref_known(v___x_660_, 1);
v___x_661_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_662_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_656_, v___x_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref_known(v___x_662_, 1);
v___x_663_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_664_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_656_, v___x_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec_ref_known(v___x_664_, 1);
v___x_665_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_666_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_667_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_668_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_669_ = l_Lean_Parser_registerAlias(v___x_665_, v___x_666_, v___x_667_, v___x_668_, v___x_650_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref_known(v___x_669_, 1);
v___x_670_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_671_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_665_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec_ref_known(v___x_671_, 1);
v___x_672_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_673_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_665_, v___x_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref_known(v___x_673_, 1);
v___x_674_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_675_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_676_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_677_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_678_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_679_ = l_Lean_Parser_registerAlias(v___x_674_, v___x_675_, v___x_676_, v___x_677_, v___x_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_679_, 1);
v___x_680_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_681_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_674_, v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref_known(v___x_681_, 1);
v___x_682_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_683_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_674_, v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref_known(v___x_683_, 1);
v___x_684_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_685_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_686_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_687_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_688_ = l_Lean_Parser_registerAlias(v___x_684_, v___x_685_, v___x_686_, v___x_687_, v___x_678_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref_known(v___x_688_, 1);
v___x_689_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_690_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_684_, v___x_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref_known(v___x_690_, 1);
v___x_691_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_692_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_684_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref_known(v___x_692_, 1);
v___x_693_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_694_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_695_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_696_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_697_ = l_Lean_Parser_registerAlias(v___x_693_, v___x_694_, v___x_695_, v___x_696_, v___x_678_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref_known(v___x_697_, 1);
v___x_698_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_699_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_693_, v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref_known(v___x_699_, 1);
v___x_700_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_701_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_693_, v___x_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref_known(v___x_701_, 1);
v___x_702_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_703_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_704_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_705_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_706_ = l_Lean_Parser_registerAlias(v___x_702_, v___x_703_, v___x_704_, v___x_705_, v___x_678_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref_known(v___x_706_, 1);
v___x_707_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_708_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_702_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v___x_708_, 1);
v___x_709_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_710_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_702_, v___x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref_known(v___x_710_, 1);
v___x_711_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_712_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_713_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_714_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_715_ = l_Lean_Parser_registerAlias(v___x_711_, v___x_712_, v___x_713_, v___x_714_, v___x_678_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref_known(v___x_715_, 1);
v___x_716_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_717_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_711_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref_known(v___x_717_, 1);
v___x_718_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_719_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_711_, v___x_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref_known(v___x_719_, 1);
v___x_720_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_721_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_722_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_723_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_724_ = l_Lean_Parser_registerAlias(v___x_720_, v___x_721_, v___x_722_, v___x_723_, v___x_678_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref_known(v___x_724_, 1);
v___x_725_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_726_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_720_, v___x_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref_known(v___x_726_, 1);
v___x_727_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_728_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_720_, v___x_727_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref_known(v___x_728_, 1);
v___x_729_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_730_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_731_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_732_ = l_Lean_Parser_registerAlias(v___x_729_, v___x_730_, v___x_731_, v___x_723_, v___x_678_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec_ref_known(v___x_732_, 1);
v___x_733_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_734_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_729_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref_known(v___x_734_, 1);
v___x_735_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_736_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_729_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref_known(v___x_736_, 1);
v___x_737_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_738_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_739_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_740_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_741_ = l_Lean_Parser_registerAlias(v___x_737_, v___x_738_, v___x_739_, v___x_740_, v___x_678_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref_known(v___x_741_, 1);
v___x_742_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_743_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_737_, v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref_known(v___x_743_, 1);
v___x_744_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_745_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_737_, v___x_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_746_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_747_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_748_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_749_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_750_ = l_Lean_Parser_registerAlias(v___x_746_, v___x_747_, v___x_748_, v___x_749_, v___x_650_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref_known(v___x_750_, 1);
v___x_751_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_752_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_746_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref_known(v___x_752_, 1);
v___x_753_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_754_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_746_, v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_755_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_756_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_757_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_758_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_759_ = l_Lean_Parser_registerAlias(v___x_755_, v___x_756_, v___x_757_, v___x_758_, v___x_650_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref_known(v___x_759_, 1);
v___x_760_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_761_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_755_, v___x_760_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref_known(v___x_761_, 1);
v___x_762_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_763_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_755_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_764_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_765_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_766_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_767_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_768_ = l_Lean_Parser_registerAlias(v___x_764_, v___x_765_, v___x_766_, v___x_767_, v___x_650_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_768_, 1);
v___x_769_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_770_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_764_, v___x_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref_known(v___x_770_, 1);
v___x_771_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_772_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_764_, v___x_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref_known(v___x_772_, 1);
v___x_773_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_774_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_775_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_776_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_777_ = l_Lean_Parser_registerAlias(v___x_773_, v___x_774_, v___x_775_, v___x_776_, v___x_650_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref_known(v___x_777_, 1);
v___x_778_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_779_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_773_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_781_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_773_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_781_, 1);
v___x_782_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_783_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_784_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_785_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_786_ = l_Lean_Parser_registerAlias(v___x_782_, v___x_783_, v___x_784_, v___x_785_, v___x_650_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_788_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_782_, v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref_known(v___x_788_, 1);
v___x_789_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_790_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_782_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_792_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_793_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_794_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_795_ = lean_box(0);
v___x_796_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_797_ = l_Lean_Parser_registerAlias(v___x_791_, v___x_792_, v___x_793_, v___x_794_, v___x_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref_known(v___x_797_, 1);
v___x_798_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_799_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_791_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_801_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_791_, v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_801_, 1);
v___x_802_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_803_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_804_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_805_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_806_ = l_Lean_Parser_registerAlias(v___x_802_, v___x_803_, v___x_804_, v___x_805_, v___x_678_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_807_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_808_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_802_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref_known(v___x_808_, 1);
v___x_809_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_810_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_802_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_812_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_813_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_814_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_815_ = l_Lean_Parser_registerAlias(v___x_811_, v___x_812_, v___x_813_, v___x_814_, v___x_678_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref_known(v___x_815_, 1);
v___x_816_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_817_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_811_, v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref_known(v___x_817_, 1);
v___x_818_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_819_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_811_, v___x_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref_known(v___x_819_, 1);
v___x_820_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_821_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_822_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_823_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_824_ = l_Lean_Parser_registerAlias(v___x_820_, v___x_821_, v___x_822_, v___x_823_, v___x_678_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref_known(v___x_824_, 1);
v___x_825_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_826_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_820_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref_known(v___x_826_, 1);
v___x_827_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_828_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_820_, v___x_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref_known(v___x_828_, 1);
v___x_829_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_830_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_831_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_832_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_833_ = l_Lean_Parser_registerAlias(v___x_829_, v___x_830_, v___x_831_, v___x_832_, v___x_678_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref_known(v___x_833_, 1);
v___x_834_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_835_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_829_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref_known(v___x_835_, 1);
v___x_836_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_837_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_829_, v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref_known(v___x_837_, 1);
v___x_838_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_839_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_840_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_841_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_842_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_843_ = l_Lean_Parser_registerAlias(v___x_838_, v___x_839_, v___x_840_, v___x_841_, v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_845_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_838_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref_known(v___x_845_, 1);
v___x_846_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_847_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_838_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v___x_847_, 1);
v___x_848_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_849_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_850_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_851_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_852_ = l_Lean_Parser_registerAlias(v___x_848_, v___x_849_, v___x_850_, v___x_851_, v___x_796_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_853_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_854_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_848_, v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref_known(v___x_854_, 1);
v___x_855_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_856_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_848_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref_known(v___x_856_, 1);
v___x_857_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_858_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_859_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_860_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_861_ = l_Lean_Parser_registerAlias(v___x_857_, v___x_858_, v___x_859_, v___x_860_, v___x_796_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_863_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_857_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref_known(v___x_863_, 1);
v___x_864_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_865_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_857_, v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_867_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_868_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_869_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_870_ = l_Lean_Parser_registerAlias(v___x_866_, v___x_867_, v___x_868_, v___x_869_, v___x_796_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref_known(v___x_870_, 1);
v___x_871_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_872_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_866_, v___x_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_872_, 1);
v___x_873_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_874_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_866_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec_ref_known(v___x_874_, 1);
v___x_875_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_876_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_877_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_878_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_879_ = l_Lean_Parser_registerAlias(v___x_875_, v___x_876_, v___x_877_, v___x_878_, v___x_678_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_881_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_875_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref_known(v___x_881_, 1);
v___x_882_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_883_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_875_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref_known(v___x_883_, 1);
v___x_884_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_885_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_886_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_887_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_888_ = l_Lean_Parser_registerAlias(v___x_884_, v___x_885_, v___x_886_, v___x_887_, v___x_678_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_889_ = lean_obj_once(&l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_, &l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
v___x_890_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_884_, v___x_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_891_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_892_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_884_, v___x_891_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref_known(v___x_892_, 1);
v___x_893_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_894_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_895_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_896_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_897_ = l_Lean_Parser_registerAlias(v___x_893_, v___x_894_, v___x_895_, v___x_896_, v___x_678_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref_known(v___x_897_, 1);
v___x_898_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_899_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_893_, v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref_known(v___x_899_, 1);
v___x_900_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_901_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_893_, v___x_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref_known(v___x_901_, 1);
v___x_902_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_903_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_904_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_905_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_906_ = l_Lean_Parser_registerAlias(v___x_902_, v___x_903_, v___x_904_, v___x_905_, v___x_796_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref_known(v___x_906_, 1);
v___x_907_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_908_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_902_, v___x_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref_known(v___x_908_, 1);
v___x_909_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_910_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_902_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_912_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_913_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_914_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_915_ = l_Lean_Parser_registerAlias(v___x_911_, v___x_912_, v___x_913_, v___x_914_, v___x_678_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref_known(v___x_915_, 1);
v___x_916_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_917_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_911_, v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_911_, v___x_800_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_919_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_920_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_921_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_922_ = l_Lean_Parser_registerAlias(v___x_919_, v___x_920_, v___x_921_, v___x_795_, v___x_678_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref_known(v___x_922_, 1);
v___x_923_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_924_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_919_, v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref_known(v___x_924_, 1);
v___x_925_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__307_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_926_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_919_, v___x_925_);
return v___x_926_;
}
else
{
return v___x_924_;
}
}
else
{
return v___x_922_;
}
}
else
{
return v___x_918_;
}
}
else
{
return v___x_917_;
}
}
else
{
return v___x_915_;
}
}
else
{
return v___x_910_;
}
}
else
{
return v___x_908_;
}
}
else
{
return v___x_906_;
}
}
else
{
return v___x_901_;
}
}
else
{
return v___x_899_;
}
}
else
{
return v___x_897_;
}
}
else
{
return v___x_892_;
}
}
else
{
return v___x_890_;
}
}
else
{
return v___x_888_;
}
}
else
{
return v___x_883_;
}
}
else
{
return v___x_881_;
}
}
else
{
return v___x_879_;
}
}
else
{
return v___x_874_;
}
}
else
{
return v___x_872_;
}
}
else
{
return v___x_870_;
}
}
else
{
return v___x_865_;
}
}
else
{
return v___x_863_;
}
}
else
{
return v___x_861_;
}
}
else
{
return v___x_856_;
}
}
else
{
return v___x_854_;
}
}
else
{
return v___x_852_;
}
}
else
{
return v___x_847_;
}
}
else
{
return v___x_845_;
}
}
else
{
return v___x_843_;
}
}
else
{
return v___x_837_;
}
}
else
{
return v___x_835_;
}
}
else
{
return v___x_833_;
}
}
else
{
return v___x_828_;
}
}
else
{
return v___x_826_;
}
}
else
{
return v___x_824_;
}
}
else
{
return v___x_819_;
}
}
else
{
return v___x_817_;
}
}
else
{
return v___x_815_;
}
}
else
{
return v___x_810_;
}
}
else
{
return v___x_808_;
}
}
else
{
return v___x_806_;
}
}
else
{
return v___x_801_;
}
}
else
{
return v___x_799_;
}
}
else
{
return v___x_797_;
}
}
else
{
return v___x_790_;
}
}
else
{
return v___x_788_;
}
}
else
{
return v___x_786_;
}
}
else
{
return v___x_781_;
}
}
else
{
return v___x_779_;
}
}
else
{
return v___x_777_;
}
}
else
{
return v___x_772_;
}
}
else
{
return v___x_770_;
}
}
else
{
return v___x_768_;
}
}
else
{
return v___x_763_;
}
}
else
{
return v___x_761_;
}
}
else
{
return v___x_759_;
}
}
else
{
return v___x_754_;
}
}
else
{
return v___x_752_;
}
}
else
{
return v___x_750_;
}
}
else
{
return v___x_745_;
}
}
else
{
return v___x_743_;
}
}
else
{
return v___x_741_;
}
}
else
{
return v___x_736_;
}
}
else
{
return v___x_734_;
}
}
else
{
return v___x_732_;
}
}
else
{
return v___x_728_;
}
}
else
{
return v___x_726_;
}
}
else
{
return v___x_724_;
}
}
else
{
return v___x_719_;
}
}
else
{
return v___x_717_;
}
}
else
{
return v___x_715_;
}
}
else
{
return v___x_710_;
}
}
else
{
return v___x_708_;
}
}
else
{
return v___x_706_;
}
}
else
{
return v___x_701_;
}
}
else
{
return v___x_699_;
}
}
else
{
return v___x_697_;
}
}
else
{
return v___x_692_;
}
}
else
{
return v___x_690_;
}
}
else
{
return v___x_688_;
}
}
else
{
return v___x_683_;
}
}
else
{
return v___x_681_;
}
}
else
{
return v___x_679_;
}
}
else
{
return v___x_673_;
}
}
else
{
return v___x_671_;
}
}
else
{
return v___x_669_;
}
}
else
{
return v___x_664_;
}
}
else
{
return v___x_662_;
}
}
else
{
return v___x_660_;
}
}
else
{
return v___x_655_;
}
}
else
{
return v___x_653_;
}
}
else
{
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
return v_res_928_;
}
}
LEAN_EXPORT lean_object* lean_mk_antiquot_parenthesizer(lean_object* v_name_929_, lean_object* v_kind_930_, uint8_t v_anonymous_931_, uint8_t v_isPseudoKind_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Parser_mkAntiquot_parenthesizer(v_name_929_, v_kind_930_, v_anonymous_931_, v_isPseudoKind_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object* v_name_939_, lean_object* v_kind_940_, lean_object* v_anonymous_941_, lean_object* v_isPseudoKind_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
uint8_t v_anonymous_boxed_948_; uint8_t v_isPseudoKind_boxed_949_; lean_object* v_res_950_; 
v_anonymous_boxed_948_ = lean_unbox(v_anonymous_941_);
v_isPseudoKind_boxed_949_ = lean_unbox(v_isPseudoKind_942_);
v_res_950_ = lean_mk_antiquot_parenthesizer(v_name_939_, v_kind_940_, v_anonymous_boxed_948_, v_isPseudoKind_boxed_949_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Parser_Term_ident_parenthesizer(v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___boxed(lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1(){
_start:
{
lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___f_974_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0));
v___x_975_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_976_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_977_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4));
v___x_978_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_975_, v___x_976_, v___x_977_, v___f_974_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___boxed(lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Parser_Term_num_parenthesizer(v_a_981_, v_a_982_, v_a_983_, v_a_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___boxed(lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___f_1001_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0));
v___x_1002_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1003_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1004_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1));
v___x_1005_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1002_, v___x_1003_, v___x_1004_, v___f_1001_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___boxed(lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Parser_Term_scientific_parenthesizer(v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___boxed(lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___f_1028_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0));
v___x_1029_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1030_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1031_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1));
v___x_1032_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1029_, v___x_1030_, v___x_1031_, v___f_1028_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___boxed(lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Parser_Term_char_parenthesizer(v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___boxed(lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___f_1055_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0));
v___x_1056_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1057_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1058_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1));
v___x_1059_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1056_, v___x_1057_, v___x_1058_, v___f_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___boxed(lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Parser_Term_str_parenthesizer(v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___boxed(lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1(){
_start:
{
lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___f_1082_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0));
v___x_1083_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1084_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1085_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1));
v___x_1086_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1083_, v___x_1084_, v___x_1085_, v___f_1082_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___boxed(lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object* v_x_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
switch(lean_obj_tag(v_x_1089_))
{
case 0:
{
lean_object* v_name_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_a_1091_);
v_name_1093_ = lean_ctor_get(v_x_1089_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1095_ = v_x_1089_;
v_isShared_1096_ = v_isSharedCheck_1122_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_name_1093_);
lean_dec(v_x_1089_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1122_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_ref_1097_ = lean_ctor_get(v_a_1090_, 2);
lean_inc(v_ref_1097_);
lean_dec_ref(v_a_1090_);
v___x_1098_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1099_ = l_Lean_Parser_getConstAlias___redArg(v___x_1098_, v_name_1093_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_ref_1097_);
lean_del_object(v___x_1095_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1121_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_io_error_to_string(v_a_1108_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 3);
lean_ctor_set(v___x_1095_, 0, v___x_1112_);
v___x_1114_ = v___x_1095_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_ref_1097_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1116_);
v___x_1118_ = v___x_1110_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
case 1:
{
lean_object* v_name_1123_; lean_object* v_p_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1156_; 
v_name_1123_ = lean_ctor_get(v_x_1089_, 0);
v_p_1124_ = lean_ctor_get(v_x_1089_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1126_ = v_x_1089_;
v_isShared_1127_ = v_isSharedCheck_1156_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_p_1124_);
lean_inc(v_name_1123_);
lean_dec(v_x_1089_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1156_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_ref_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_ref_1128_ = lean_ctor_get(v_a_1090_, 2);
v___x_1129_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1130_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1129_, v_name_1123_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1126_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1124_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_apply_1(v_a_1131_, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_dec(v_a_1131_);
return v___x_1132_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1155_; 
lean_inc(v_ref_1128_);
lean_dec_ref(v_p_1124_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_a_1142_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1144_ = v___x_1130_;
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1130_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1146_ = lean_io_error_to_string(v_a_1142_);
v___x_1147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofFormat(v___x_1147_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 0);
lean_ctor_set(v___x_1126_, 1, v___x_1148_);
lean_ctor_set(v___x_1126_, 0, v_ref_1128_);
v___x_1150_ = v___x_1126_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_ref_1128_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1150_);
v___x_1152_ = v___x_1144_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
case 2:
{
lean_object* v_name_1157_; lean_object* v_p_u2081_1158_; lean_object* v_p_u2082_1159_; lean_object* v_ref_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_name_1157_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_name_1157_);
v_p_u2081_1158_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_p_u2081_1158_);
v_p_u2082_1159_ = lean_ctor_get(v_x_1089_, 2);
lean_inc_ref(v_p_u2082_1159_);
lean_dec_ref_known(v_x_1089_, 3);
v_ref_1160_ = lean_ctor_get(v_a_1090_, 2);
v___x_1161_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
v___x_1162_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1161_, v_name_1157_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
v___x_1164_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_u2081_1158_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_u2082_1159_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_apply_2(v_a_1163_, v_a_1165_, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_dec(v_a_1165_);
lean_dec(v_a_1163_);
return v___x_1166_;
}
}
else
{
lean_dec(v_a_1163_);
lean_dec_ref(v_p_u2082_1159_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v___x_1164_;
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1187_; 
lean_inc(v_ref_1160_);
lean_dec_ref(v_p_u2082_1159_);
lean_dec_ref(v_p_u2081_1158_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_a_1176_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1178_ = v___x_1162_;
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1162_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1180_ = lean_io_error_to_string(v_a_1176_);
v___x_1181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
v___x_1182_ = l_Lean_MessageData_ofFormat(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_ref_1160_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1183_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
case 3:
{
lean_object* v_kind_1188_; lean_object* v_prec_1189_; lean_object* v_p_1190_; lean_object* v___x_1191_; 
v_kind_1188_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_kind_1188_);
v_prec_1189_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_prec_1189_);
v_p_1190_ = lean_ctor_get(v_x_1089_, 2);
lean_inc_ref(v_p_1190_);
lean_dec_ref_known(v_x_1089_, 3);
v___x_1191_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1190_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1196_, 0, v_kind_1188_);
lean_closure_set(v___x_1196_, 1, v_prec_1189_);
lean_closure_set(v___x_1196_, 2, v_a_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_dec(v_prec_1189_);
lean_dec(v_kind_1188_);
return v___x_1191_;
}
}
case 4:
{
lean_object* v_kind_1201_; lean_object* v_prec_1202_; lean_object* v_lhsPrec_1203_; lean_object* v_p_1204_; lean_object* v___x_1205_; 
v_kind_1201_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_kind_1201_);
v_prec_1202_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_prec_1202_);
v_lhsPrec_1203_ = lean_ctor_get(v_x_1089_, 2);
lean_inc(v_lhsPrec_1203_);
v_p_1204_ = lean_ctor_get(v_x_1089_, 3);
lean_inc_ref(v_p_1204_);
lean_dec_ref_known(v_x_1089_, 4);
v___x_1205_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1204_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1210_, 0, v_kind_1201_);
lean_closure_set(v___x_1210_, 1, v_prec_1202_);
lean_closure_set(v___x_1210_, 2, v_lhsPrec_1203_);
lean_closure_set(v___x_1210_, 3, v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_dec(v_lhsPrec_1203_);
lean_dec(v_prec_1202_);
lean_dec(v_kind_1201_);
return v___x_1205_;
}
}
case 5:
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_val_1215_ = lean_ctor_get(v_x_1089_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_x_1089_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v_x_1089_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1219_, 0, v_val_1215_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
case 6:
{
lean_object* v_val_1224_; uint8_t v_includeIdent_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_val_1224_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_val_1224_);
v_includeIdent_1225_ = lean_ctor_get_uint8(v_x_1089_, sizeof(void*)*1);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1226_ = lean_box(v_includeIdent_1225_);
v___x_1227_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1227_, 0, v_val_1224_);
lean_closure_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
case 7:
{
lean_object* v_catName_1229_; lean_object* v_rbp_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_catName_1229_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_catName_1229_);
v_rbp_1230_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_rbp_1230_);
lean_dec_ref_known(v_x_1089_, 2);
v___x_1231_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1231_, 0, v_catName_1229_);
lean_closure_set(v___x_1231_, 1, v_rbp_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
case 8:
{
lean_object* v_declName_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_declName_1233_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_declName_1233_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1234_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
v___x_1235_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v___x_1234_, v_declName_1233_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v___x_1235_;
}
case 9:
{
lean_object* v_name_1236_; lean_object* v_kind_1237_; lean_object* v_p_1238_; lean_object* v___x_1239_; 
v_name_1236_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_name_1236_);
v_kind_1237_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_kind_1237_);
v_p_1238_ = lean_ctor_get(v_x_1089_, 2);
lean_inc_ref(v_p_1238_);
lean_dec_ref_known(v_x_1089_, 3);
v___x_1239_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1238_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1254_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1244_ = 1;
v___x_1245_ = 0;
v___x_1246_ = lean_box(v___x_1244_);
v___x_1247_ = lean_box(v___x_1245_);
lean_inc(v_kind_1237_);
v___x_1248_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 9, 4);
lean_closure_set(v___x_1248_, 0, v_name_1236_);
lean_closure_set(v___x_1248_, 1, v_kind_1237_);
lean_closure_set(v___x_1248_, 2, v___x_1246_);
lean_closure_set(v___x_1248_, 3, v___x_1247_);
v___x_1249_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1249_, 0, v_kind_1237_);
lean_closure_set(v___x_1249_, 1, v_a_1240_);
v___x_1250_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1250_, 0, v___x_1248_);
lean_closure_set(v___x_1250_, 1, v___x_1249_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1250_);
v___x_1252_ = v___x_1242_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_dec(v_kind_1237_);
lean_dec_ref(v_name_1236_);
return v___x_1239_;
}
}
case 10:
{
lean_object* v_p_1255_; lean_object* v_sep_1256_; lean_object* v_psep_1257_; uint8_t v_allowTrailingSep_1258_; lean_object* v___x_1259_; 
v_p_1255_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_p_1255_);
v_sep_1256_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_sep_1256_);
v_psep_1257_ = lean_ctor_get(v_x_1089_, 2);
lean_inc_ref(v_psep_1257_);
v_allowTrailingSep_1258_ = lean_ctor_get_uint8(v_x_1089_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1089_, 3);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
v___x_1259_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1255_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_psep_1257_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1271_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = lean_box(v_allowTrailingSep_1258_);
v___x_1267_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1267_, 0, v_a_1260_);
lean_closure_set(v___x_1267_, 1, v_sep_1256_);
lean_closure_set(v___x_1267_, 2, v_a_1262_);
lean_closure_set(v___x_1267_, 3, v___x_1266_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_dec(v_a_1260_);
lean_dec_ref(v_sep_1256_);
return v___x_1261_;
}
}
else
{
lean_dec_ref(v_psep_1257_);
lean_dec_ref(v_sep_1256_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v___x_1259_;
}
}
case 11:
{
lean_object* v_p_1272_; lean_object* v_sep_1273_; lean_object* v_psep_1274_; uint8_t v_allowTrailingSep_1275_; lean_object* v___x_1276_; 
v_p_1272_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_p_1272_);
v_sep_1273_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_sep_1273_);
v_psep_1274_ = lean_ctor_get(v_x_1089_, 2);
lean_inc_ref(v_psep_1274_);
v_allowTrailingSep_1275_ = lean_ctor_get_uint8(v_x_1089_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1089_, 3);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
v___x_1276_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_p_1272_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_psep_1274_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1288_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = lean_box(v_allowTrailingSep_1275_);
v___x_1284_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1284_, 0, v_a_1277_);
lean_closure_set(v___x_1284_, 1, v_sep_1273_);
lean_closure_set(v___x_1284_, 2, v_a_1279_);
lean_closure_set(v___x_1284_, 3, v___x_1283_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_dec(v_a_1277_);
lean_dec_ref(v_sep_1273_);
return v___x_1278_;
}
}
else
{
lean_dec_ref(v_psep_1274_);
lean_dec_ref(v_sep_1273_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v___x_1276_;
}
}
default: 
{
lean_object* v_val_1289_; lean_object* v_asciiVal_1290_; uint8_t v_preserveForPP_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
v_val_1289_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_val_1289_);
v_asciiVal_1290_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_asciiVal_1290_);
v_preserveForPP_1291_ = lean_ctor_get_uint8(v_x_1089_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1089_, 2);
v___x_1292_ = lean_box(v_preserveForPP_1291_);
v___x_1293_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbol_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1293_, 0, v_val_1289_);
lean_closure_set(v___x_1293_, 1, v_asciiVal_1290_);
lean_closure_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___boxed(lean_object* v_x_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(v_x_1295_, v_a_1296_, v_a_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* lean_mk_antiquot_formatter(lean_object* v_name_1300_, lean_object* v_kind_1301_, uint8_t v_anonymous_1302_, uint8_t v_isPseudoKind_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Parser_mkAntiquot_formatter(v_name_1300_, v_kind_1301_, v_anonymous_1302_, v_isPseudoKind_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object* v_name_1310_, lean_object* v_kind_1311_, lean_object* v_anonymous_1312_, lean_object* v_isPseudoKind_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
uint8_t v_anonymous_boxed_1319_; uint8_t v_isPseudoKind_boxed_1320_; lean_object* v_res_1321_; 
v_anonymous_boxed_1319_ = lean_unbox(v_anonymous_1312_);
v_isPseudoKind_boxed_1320_ = lean_unbox(v_isPseudoKind_1313_);
v_res_1321_ = lean_mk_antiquot_formatter(v_name_1310_, v_kind_1311_, v_anonymous_boxed_1319_, v_isPseudoKind_boxed_1320_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Parser_Term_ident_formatter(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter___boxed(lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_PrettyPrinter_Formatter_ident_formatter(v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1(){
_start:
{
lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___f_1344_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0));
v___x_1345_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1346_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1347_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3));
v___x_1348_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1345_, v___x_1346_, v___x_1347_, v___f_1344_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___boxed(lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Parser_Term_num_formatter(v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter___boxed(lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_PrettyPrinter_Formatter_numLit_formatter(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1(){
_start:
{
lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___f_1371_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0));
v___x_1372_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1373_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1374_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1));
v___x_1375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1372_, v___x_1373_, v___x_1374_, v___f_1371_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___boxed(lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Parser_Term_scientific_formatter(v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter___boxed(lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1(){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___f_1398_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0));
v___x_1399_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1400_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1401_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1));
v___x_1402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1399_, v___x_1400_, v___x_1401_, v___f_1398_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___boxed(lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Parser_Term_char_formatter(v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter___boxed(lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_PrettyPrinter_Formatter_charLit_formatter(v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1(){
_start:
{
lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___f_1425_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0));
v___x_1426_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1427_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1428_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1));
v___x_1429_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1426_, v___x_1427_, v___x_1428_, v___f_1425_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___boxed(lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Parser_Term_str_formatter(v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter___boxed(lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_PrettyPrinter_Formatter_strLit_formatter(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1(){
_start:
{
lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___f_1452_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0));
v___x_1453_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1454_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_));
v___x_1455_ = ((lean_object*)(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1));
v___x_1456_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1453_, v___x_1454_, v___x_1455_, v___f_1452_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___boxed(lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1459_, v___x_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed(lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(v___x_1467_, v___x_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* v_x_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
switch(lean_obj_tag(v_x_1475_))
{
case 0:
{
lean_object* v_name_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1477_);
v_name_1479_ = lean_ctor_get(v_x_1475_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1481_ = v_x_1475_;
v_isShared_1482_ = v_isSharedCheck_1508_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_name_1479_);
lean_dec(v_x_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1508_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_ref_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_ref_1483_ = lean_ctor_get(v_a_1476_, 2);
lean_inc(v_ref_1483_);
lean_dec_ref(v_a_1476_);
v___x_1484_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1485_ = l_Lean_Parser_getConstAlias___redArg(v___x_1484_, v_name_1479_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_ref_1483_);
lean_del_object(v___x_1481_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1507_; 
v_a_1494_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1496_ = v___x_1485_;
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1485_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_io_error_to_string(v_a_1494_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 3);
lean_ctor_set(v___x_1481_, 0, v___x_1498_);
v___x_1500_ = v___x_1481_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = l_Lean_MessageData_ofFormat(v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_ref_1483_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1502_);
v___x_1504_ = v___x_1496_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
case 1:
{
lean_object* v_name_1509_; lean_object* v_p_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1542_; 
v_name_1509_ = lean_ctor_get(v_x_1475_, 0);
v_p_1510_ = lean_ctor_get(v_x_1475_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1512_ = v_x_1475_;
v_isShared_1513_ = v_isSharedCheck_1542_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_p_1510_);
lean_inc(v_name_1509_);
lean_dec(v_x_1475_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1542_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_ref_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_ref_1514_ = lean_ctor_get(v_a_1476_, 2);
v___x_1515_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1516_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1515_, v_name_1509_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
lean_del_object(v___x_1512_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1510_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_apply_1(v_a_1517_, v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_dec(v_a_1517_);
return v___x_1518_;
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1541_; 
lean_inc(v_ref_1514_);
lean_dec_ref(v_p_1510_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_a_1528_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1530_ = v___x_1516_;
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1516_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1532_ = lean_io_error_to_string(v_a_1528_);
v___x_1533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
v___x_1534_ = l_Lean_MessageData_ofFormat(v___x_1533_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 0);
lean_ctor_set(v___x_1512_, 1, v___x_1534_);
lean_ctor_set(v___x_1512_, 0, v_ref_1514_);
v___x_1536_ = v___x_1512_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_ref_1514_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1538_ = v___x_1530_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
case 2:
{
lean_object* v_name_1543_; lean_object* v_p_u2081_1544_; lean_object* v_p_u2082_1545_; lean_object* v_ref_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_name_1543_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_name_1543_);
v_p_u2081_1544_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_p_u2081_1544_);
v_p_u2082_1545_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_p_u2082_1545_);
lean_dec_ref_known(v_x_1475_, 3);
v_ref_1546_ = lean_ctor_get(v_a_1476_, 2);
v___x_1547_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
v___x_1548_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1547_, v_name_1543_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
lean_inc(v_a_1477_);
lean_inc_ref(v_a_1476_);
v___x_1550_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_u2081_1544_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_u2082_1545_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_apply_2(v_a_1549_, v_a_1551_, v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec(v_a_1551_);
lean_dec(v_a_1549_);
return v___x_1552_;
}
}
else
{
lean_dec(v_a_1549_);
lean_dec_ref(v_p_u2082_1545_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v___x_1550_;
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1573_; 
lean_inc(v_ref_1546_);
lean_dec_ref(v_p_u2082_1545_);
lean_dec_ref(v_p_u2081_1544_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_a_1562_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1564_ = v___x_1548_;
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1548_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1566_ = lean_io_error_to_string(v_a_1562_);
v___x_1567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
v___x_1568_ = l_Lean_MessageData_ofFormat(v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_ref_1546_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1569_);
v___x_1571_ = v___x_1564_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
case 3:
{
lean_object* v_kind_1574_; lean_object* v_p_1575_; lean_object* v___x_1576_; 
v_kind_1574_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_kind_1574_);
v_p_1575_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_p_1575_);
lean_dec_ref_known(v_x_1475_, 3);
v___x_1576_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1575_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_1581_, 0, v_kind_1574_);
lean_closure_set(v___x_1581_, 1, v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_dec(v_kind_1574_);
return v___x_1576_;
}
}
case 4:
{
lean_object* v_kind_1586_; lean_object* v_prec_1587_; lean_object* v_lhsPrec_1588_; lean_object* v_p_1589_; lean_object* v___x_1590_; 
v_kind_1586_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_kind_1586_);
v_prec_1587_ = lean_ctor_get(v_x_1475_, 1);
lean_inc(v_prec_1587_);
v_lhsPrec_1588_ = lean_ctor_get(v_x_1475_, 2);
lean_inc(v_lhsPrec_1588_);
v_p_1589_ = lean_ctor_get(v_x_1475_, 3);
lean_inc_ref(v_p_1589_);
lean_dec_ref_known(v_x_1475_, 4);
v___x_1590_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1589_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed), 9, 4);
lean_closure_set(v___x_1595_, 0, v_kind_1586_);
lean_closure_set(v___x_1595_, 1, v_prec_1587_);
lean_closure_set(v___x_1595_, 2, v_lhsPrec_1588_);
lean_closure_set(v___x_1595_, 3, v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_dec(v_lhsPrec_1588_);
lean_dec(v_prec_1587_);
lean_dec(v_kind_1586_);
return v___x_1590_;
}
}
case 5:
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_val_1600_ = lean_ctor_get(v_x_1475_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_x_1475_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v_x_1475_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter___boxed), 6, 1);
lean_closure_set(v___x_1604_, 0, v_val_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
case 6:
{
lean_object* v_val_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_val_1609_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_val_1609_);
lean_dec_ref_known(v_x_1475_, 1);
v___x_1610_ = 0;
v___x_1611_ = lean_box(v___x_1610_);
v___x_1612_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(v___x_1612_, 0, v_val_1609_);
lean_closure_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
case 7:
{
lean_object* v_catName_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_catName_1614_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_catName_1614_);
lean_dec_ref_known(v_x_1475_, 2);
v___x_1615_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed), 6, 1);
lean_closure_set(v___x_1615_, 0, v_catName_1614_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
case 8:
{
lean_object* v_declName_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_declName_1617_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_declName_1617_);
lean_dec_ref_known(v_x_1475_, 1);
v___x_1618_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
v___x_1619_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v___x_1618_, v_declName_1617_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v___x_1619_;
}
case 9:
{
lean_object* v_name_1620_; lean_object* v_kind_1621_; lean_object* v_p_1622_; lean_object* v___x_1623_; 
v_name_1620_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_name_1620_);
v_kind_1621_ = lean_ctor_get(v_x_1475_, 1);
lean_inc(v_kind_1621_);
v_p_1622_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_p_1622_);
lean_dec_ref_known(v_x_1475_, 3);
v___x_1623_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1622_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1638_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
uint8_t v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___x_1636_; 
v___x_1628_ = 1;
v___x_1629_ = 0;
v___x_1630_ = lean_box(v___x_1628_);
v___x_1631_ = lean_box(v___x_1629_);
lean_inc(v_kind_1621_);
v___x_1632_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(v___x_1632_, 0, v_name_1620_);
lean_closure_set(v___x_1632_, 1, v_kind_1621_);
lean_closure_set(v___x_1632_, 2, v___x_1630_);
lean_closure_set(v___x_1632_, 3, v___x_1631_);
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_1633_, 0, v_kind_1621_);
lean_closure_set(v___x_1633_, 1, v_a_1624_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1634_, 0, v___x_1632_);
lean_closure_set(v___f_1634_, 1, v___x_1633_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___f_1634_);
v___x_1636_ = v___x_1626_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___f_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_dec(v_kind_1621_);
lean_dec_ref(v_name_1620_);
return v___x_1623_;
}
}
case 10:
{
lean_object* v_p_1639_; lean_object* v_sep_1640_; lean_object* v_psep_1641_; uint8_t v_allowTrailingSep_1642_; lean_object* v___x_1643_; 
v_p_1639_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_p_1639_);
v_sep_1640_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_sep_1640_);
v_psep_1641_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_psep_1641_);
v_allowTrailingSep_1642_ = lean_ctor_get_uint8(v_x_1475_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1475_, 3);
lean_inc(v_a_1477_);
lean_inc_ref(v_a_1476_);
v___x_1643_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1639_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = lean_pretty_printer_formatter_interpret_parser_descr(v_psep_1641_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1650_ = lean_box(v_allowTrailingSep_1642_);
v___x_1651_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_formatter___boxed), 9, 4);
lean_closure_set(v___x_1651_, 0, v_a_1644_);
lean_closure_set(v___x_1651_, 1, v_sep_1640_);
lean_closure_set(v___x_1651_, 2, v_a_1646_);
lean_closure_set(v___x_1651_, 3, v___x_1650_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_dec(v_a_1644_);
lean_dec_ref(v_sep_1640_);
return v___x_1645_;
}
}
else
{
lean_dec_ref(v_psep_1641_);
lean_dec_ref(v_sep_1640_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v___x_1643_;
}
}
case 11:
{
lean_object* v_p_1656_; lean_object* v_sep_1657_; lean_object* v_psep_1658_; uint8_t v_allowTrailingSep_1659_; lean_object* v___x_1660_; 
v_p_1656_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_p_1656_);
v_sep_1657_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_sep_1657_);
v_psep_1658_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_psep_1658_);
v_allowTrailingSep_1659_ = lean_ctor_get_uint8(v_x_1475_, sizeof(void*)*3);
lean_dec_ref_known(v_x_1475_, 3);
lean_inc(v_a_1477_);
lean_inc_ref(v_a_1476_);
v___x_1660_ = lean_pretty_printer_formatter_interpret_parser_descr(v_p_1656_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = lean_pretty_printer_formatter_interpret_parser_descr(v_psep_1658_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1672_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_box(v_allowTrailingSep_1659_);
v___x_1668_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_1668_, 0, v_a_1661_);
lean_closure_set(v___x_1668_, 1, v_sep_1657_);
lean_closure_set(v___x_1668_, 2, v_a_1663_);
lean_closure_set(v___x_1668_, 3, v___x_1667_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_dec(v_a_1661_);
lean_dec_ref(v_sep_1657_);
return v___x_1662_;
}
}
else
{
lean_dec_ref(v_psep_1658_);
lean_dec_ref(v_sep_1657_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v___x_1660_;
}
}
default: 
{
lean_object* v_val_1673_; lean_object* v_asciiVal_1674_; uint8_t v_preserveForPP_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
v_val_1673_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_val_1673_);
v_asciiVal_1674_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_asciiVal_1674_);
v_preserveForPP_1675_ = lean_ctor_get_uint8(v_x_1475_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1475_, 2);
v___x_1676_ = lean_box(v_preserveForPP_1675_);
v___x_1677_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbol_formatter___boxed), 8, 3);
lean_closure_set(v___x_1677_, 0, v_val_1673_);
lean_closure_set(v___x_1677_, 1, v_asciiVal_1674_);
lean_closure_set(v___x_1677_, 2, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___boxed(lean_object* v_x_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = lean_pretty_printer_formatter_interpret_parser_descr(v_x_1679_, v_a_1680_, v_a_1681_);
return v_res_1683_;
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
