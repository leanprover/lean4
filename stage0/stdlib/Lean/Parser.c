// Lean compiler output
// Module: Lean.Parser
// Imports: Init Lean.Parser.Basic Lean.Parser.Level Lean.Parser.Term Lean.Parser.Tactic Lean.Parser.Command Lean.Parser.Module Lean.Parser.Syntax Lean.Parser.Do
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
extern lean_object* l_Lean_Parser_Command_structFields___elambda__1___closed__6;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14;
lean_object* l_Lean_Parser_getBinaryAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5;
lean_object* l_Lean_Parser_lookahead(lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__11;
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_charLit;
extern lean_object* l_Lean_Parser_errorAtSavedPos___closed__1;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__12;
extern lean_object* l_Lean_Parser_ident;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7;
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1162____closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_leadingNode_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1;
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_symbol_parenthesizer___rarg___closed__1;
extern lean_object* l_term___x24_______closed__8;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1;
extern lean_object* l_term___x24_______closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6(lean_object*, uint8_t);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
extern lean_object* l_termS_x21_____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1;
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__10;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*);
extern lean_object* l_Lean_scientificLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29;
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserAliasesRef;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_958____closed__6;
extern lean_object* l_Lean_Parser_Tactic_location___closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33;
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
extern lean_object* l_Lean_numLitKind___closed__2;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1264____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11;
extern lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2907____closed__14;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__5;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3;
extern lean_object* l_Lean_Parser_instOrElseParser___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__3;
lean_object* l_Lean_Parser_getConstAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getUnaryAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15;
extern lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18;
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1060____closed__4;
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
extern lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___boxed(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2907____closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17;
lean_object* l_Lean_Parser_sepBy_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_object*);
extern lean_object* l_Lean_Parser_instAndThenParser___closed__1;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2054____closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21;
extern lean_object* l_rawNatLit___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__6;
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__6;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_match__1(lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__16;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1;
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__8;
lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("element");
return x_1;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("space before");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1;
x_2 = l_Lean_Parser_checkWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("line break");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6;
x_2 = l_Lean_Parser_checkLinebreakBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_Term_type___elambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_Command_structFields___elambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_lookahead), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_atomic), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_many), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_many1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_optional), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instOrElseParser___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instAndThenParser___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_parserAliasesRef;
x_3 = l_term___x24_______closed__8;
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_term_____x5b___x3a___x5d___closed__6;
x_8 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2907____closed__6;
x_12 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_rawNatLit___closed__6;
x_16 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9;
x_17 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_15, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__8;
x_20 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10;
x_21 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__12;
x_24 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11;
x_25 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_23, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__16;
x_28 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12;
x_29 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_27, x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_identKind___closed__2;
x_32 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13;
x_33 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Parser_Tactic_intro___closed__10;
x_36 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15;
x_37 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_35, x_36, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Parser_Tactic_inductionAlts___closed__8;
x_40 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17;
x_41 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_39, x_40, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2907____closed__14;
x_44 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19;
x_45 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_43, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_term___x24_______closed__4;
x_48 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21;
x_49 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_47, x_48, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_1060____closed__4;
x_52 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23;
x_53 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_51, x_52, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_myMacro____x40_Init_Notation___hyg_958____closed__6;
x_56 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25;
x_57 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_55, x_56, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_2054____closed__4;
x_60 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27;
x_61 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_59, x_60, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_myMacro____x40_Init_Notation___hyg_1162____closed__4;
x_64 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29;
x_65 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_63, x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Parser_Tactic_location___closed__4;
x_68 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31;
x_69 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_67, x_68, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_termS_x21_____closed__6;
x_72 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33;
x_73 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_71, x_72, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_myMacro____x40_Init_Notation___hyg_1264____closed__6;
x_76 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34;
x_77 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_75, x_76, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_80 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35;
x_81 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_79, x_80, x_78);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_69);
if (x_90 == 0)
{
return x_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_69, 0);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_69);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_65);
if (x_94 == 0)
{
return x_65;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_65, 0);
x_96 = lean_ctor_get(x_65, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_65);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_61);
if (x_98 == 0)
{
return x_61;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_61, 0);
x_100 = lean_ctor_get(x_61, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_61);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_57);
if (x_102 == 0)
{
return x_57;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_57, 0);
x_104 = lean_ctor_get(x_57, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_57);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_53);
if (x_106 == 0)
{
return x_53;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_53, 0);
x_108 = lean_ctor_get(x_53, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_53);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_49);
if (x_110 == 0)
{
return x_49;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_49, 0);
x_112 = lean_ctor_get(x_49, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_49);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_45);
if (x_114 == 0)
{
return x_45;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_45, 0);
x_116 = lean_ctor_get(x_45, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_45);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_41);
if (x_118 == 0)
{
return x_41;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_41, 0);
x_120 = lean_ctor_get(x_41, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_41);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_37);
if (x_122 == 0)
{
return x_37;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_37, 0);
x_124 = lean_ctor_get(x_37, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_37);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_33);
if (x_126 == 0)
{
return x_33;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_33, 0);
x_128 = lean_ctor_get(x_33, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_33);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_29);
if (x_130 == 0)
{
return x_29;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_29, 0);
x_132 = lean_ctor_get(x_29, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_29);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_25);
if (x_134 == 0)
{
return x_25;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_25, 0);
x_136 = lean_ctor_get(x_25, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_25);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_21);
if (x_138 == 0)
{
return x_21;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_21, 0);
x_140 = lean_ctor_get(x_21, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_21);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_17);
if (x_142 == 0)
{
return x_17;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_17, 0);
x_144 = lean_ctor_get(x_17, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_17);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_13);
if (x_146 == 0)
{
return x_13;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_13, 0);
x_148 = lean_ctor_get(x_13, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_13);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_9);
if (x_150 == 0)
{
return x_9;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_9, 0);
x_152 = lean_ctor_get(x_9, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_9);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_5);
if (x_154 == 0)
{
return x_5;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_5, 0);
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_5);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
lean_object* lean_mk_antiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_numLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_scientificLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_charLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_strLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_3, x_16, x_17);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_3(x_4, x_19, x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_apply_3(x_5, x_23, x_24, x_25);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_3(x_9, x_27, x_28, x_29);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_1(x_10, x_31);
return x_32;
}
case 6:
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_35 = lean_box(x_34);
x_36 = lean_apply_2(x_11, x_33, x_35);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_apply_2(x_13, x_37, x_38);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_apply_1(x_12, x_40);
return x_41;
}
case 9:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_apply_3(x_6, x_42, x_43, x_44);
return x_45;
}
case 10:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box(x_49);
x_51 = lean_apply_4(x_7, x_46, x_47, x_48, x_50);
return x_51;
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_56 = lean_box(x_55);
x_57 = lean_apply_4(x_8, x_52, x_53, x_54, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_match__1___rarg), 13, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_symbol_parenthesizer___rarg___closed__1;
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_nonReservedSymbol_parenthesizer___rarg___closed__1;
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_parenthesizer(x_3, x_1, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_parenthesizer(x_3, x_1, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_st_ref_get(x_3, x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_10 = l_Lean_Parser_getConstAlias___rarg(x_9, x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_io_error_to_string(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_io_error_to_string(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_st_ref_get(x_3, x_4);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_34 = l_Lean_Parser_getUnaryAlias___rarg(x_33, x_28, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_29, x_2, x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_40, 0, x_35);
lean_closure_set(x_40, 1, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_43, 0, x_35);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_35);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_io_error_to_string(x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_34, 0, x_54);
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_io_error_to_string(x_55);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_32);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_st_ref_get(x_3, x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_2, 3);
lean_inc(x_67);
x_68 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_69 = l_Lean_Parser_getBinaryAlias___rarg(x_68, x_62, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_3);
lean_inc(x_2);
x_72 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_63, x_2, x_3, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_64, x_2, x_3, x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_78, 0, x_70);
lean_closure_set(x_78, 1, x_73);
lean_closure_set(x_78, 2, x_77);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_81, 0, x_70);
lean_closure_set(x_81, 1, x_73);
lean_closure_set(x_81, 2, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_73);
lean_dec(x_70);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_70);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_69);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_69, 0);
x_93 = lean_io_error_to_string(x_92);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_67);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_69, 0, x_96);
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_69, 0);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_69);
x_99 = lean_io_error_to_string(x_97);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_67);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
}
}
case 3:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_inc(x_106);
lean_dec(x_1);
x_107 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_106, x_2, x_3, x_4);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3___boxed), 8, 3);
lean_closure_set(x_110, 0, x_104);
lean_closure_set(x_110, 1, x_105);
lean_closure_set(x_110, 2, x_109);
lean_ctor_set(x_107, 0, x_110);
return x_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_107, 0);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_107);
x_113 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3___boxed), 8, 3);
lean_closure_set(x_113, 0, x_104);
lean_closure_set(x_113, 1, x_105);
lean_closure_set(x_113, 2, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_105);
lean_dec(x_104);
x_115 = !lean_is_exclusive(x_107);
if (x_115 == 0)
{
return x_107;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_107, 0);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_107);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
case 4:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_1, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 2);
lean_inc(x_121);
lean_dec(x_1);
x_122 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_121, x_2, x_3, x_4);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__4), 8, 3);
lean_closure_set(x_125, 0, x_119);
lean_closure_set(x_125, 1, x_120);
lean_closure_set(x_125, 2, x_124);
lean_ctor_set(x_122, 0, x_125);
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__4), 8, 3);
lean_closure_set(x_128, 0, x_119);
lean_closure_set(x_128, 1, x_120);
lean_closure_set(x_128, 2, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_120);
lean_dec(x_119);
x_130 = !lean_is_exclusive(x_122);
if (x_130 == 0)
{
return x_122;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_122, 0);
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_122);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
case 5:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___rarg), 5, 0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_4);
return x_135;
}
case 6:
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___rarg), 5, 0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_4);
return x_137;
}
case 7:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
lean_dec(x_1);
x_140 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__7), 7, 2);
lean_closure_set(x_140, 0, x_138);
lean_closure_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_4);
return x_141;
}
case 8:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
lean_dec(x_1);
x_143 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_144 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(x_143, x_142, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_144;
}
case 9:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_1, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 2);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_146, x_2, x_3, x_4);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_150, 0, x_145);
lean_closure_set(x_150, 1, x_149);
lean_ctor_set(x_147, 0, x_150);
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_147);
x_153 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_153, 0, x_145);
lean_closure_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_145);
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
return x_147;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_147, 0);
x_157 = lean_ctor_get(x_147, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_147);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
case 10:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_163 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_159, x_2, x_3, x_4);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_161, x_2, x_3, x_165);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_box(x_162);
x_170 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9___boxed), 9, 4);
lean_closure_set(x_170, 0, x_160);
lean_closure_set(x_170, 1, x_169);
lean_closure_set(x_170, 2, x_164);
lean_closure_set(x_170, 3, x_168);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_166, 0);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_166);
x_173 = lean_box(x_162);
x_174 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9___boxed), 9, 4);
lean_closure_set(x_174, 0, x_160);
lean_closure_set(x_174, 1, x_173);
lean_closure_set(x_174, 2, x_164);
lean_closure_set(x_174, 3, x_171);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_164);
lean_dec(x_160);
x_176 = !lean_is_exclusive(x_166);
if (x_176 == 0)
{
return x_166;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_166, 0);
x_178 = lean_ctor_get(x_166, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_166);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_163);
if (x_180 == 0)
{
return x_163;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_163, 0);
x_182 = lean_ctor_get(x_163, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_163);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 2);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_188 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_184, x_2, x_3, x_4);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_186, x_2, x_3, x_190);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_box(x_187);
x_195 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10___boxed), 9, 4);
lean_closure_set(x_195, 0, x_185);
lean_closure_set(x_195, 1, x_194);
lean_closure_set(x_195, 2, x_189);
lean_closure_set(x_195, 3, x_193);
lean_ctor_set(x_191, 0, x_195);
return x_191;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_191, 0);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_191);
x_198 = lean_box(x_187);
x_199 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10___boxed), 9, 4);
lean_closure_set(x_199, 0, x_185);
lean_closure_set(x_199, 1, x_198);
lean_closure_set(x_199, 2, x_189);
lean_closure_set(x_199, 3, x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
uint8_t x_201; 
lean_dec(x_189);
lean_dec(x_185);
x_201 = !lean_is_exclusive(x_191);
if (x_201 == 0)
{
return x_191;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_191, 0);
x_203 = lean_ctor_get(x_191, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_191);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
return x_188;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_188);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__6(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__9(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___elambda__10(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* lean_mk_antiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_formatter(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__11;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_ident_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_numLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_scientificLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__7;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_charLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_strLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Parser_nonReservedSymbol_formatter(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_formatter(x_3, x_1, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_formatter(x_3, x_1, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_st_ref_get(x_3, x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_10 = l_Lean_Parser_getConstAlias___rarg(x_9, x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_io_error_to_string(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_io_error_to_string(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_st_ref_get(x_3, x_4);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
x_33 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_34 = l_Lean_Parser_getUnaryAlias___rarg(x_33, x_28, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_pretty_printer_formatter_interpret_parser_descr(x_29, x_2, x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_40, 0, x_35);
lean_closure_set(x_40, 1, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_43, 0, x_35);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_35);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_io_error_to_string(x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_34, 0, x_54);
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_io_error_to_string(x_55);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_32);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_st_ref_get(x_3, x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_2, 3);
lean_inc(x_67);
x_68 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_69 = l_Lean_Parser_getBinaryAlias___rarg(x_68, x_62, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_3);
lean_inc(x_2);
x_72 = lean_pretty_printer_formatter_interpret_parser_descr(x_63, x_2, x_3, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_pretty_printer_formatter_interpret_parser_descr(x_64, x_2, x_3, x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_78, 0, x_70);
lean_closure_set(x_78, 1, x_73);
lean_closure_set(x_78, 2, x_77);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_81, 0, x_70);
lean_closure_set(x_81, 1, x_73);
lean_closure_set(x_81, 2, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_73);
lean_dec(x_70);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_70);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_69);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_69, 0);
x_93 = lean_io_error_to_string(x_92);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_67);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_69, 0, x_96);
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_69, 0);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_69);
x_99 = lean_io_error_to_string(x_97);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_67);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
}
}
case 3:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 2);
lean_inc(x_105);
lean_dec(x_1);
x_106 = lean_pretty_printer_formatter_interpret_parser_descr(x_105, x_2, x_3, x_4);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 7, 2);
lean_closure_set(x_109, 0, x_104);
lean_closure_set(x_109, 1, x_108);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 7, 2);
lean_closure_set(x_112, 0, x_104);
lean_closure_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_104);
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_106, 0);
x_116 = lean_ctor_get(x_106, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_106);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 4:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_pretty_printer_formatter_interpret_parser_descr(x_120, x_2, x_3, x_4);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 8, 3);
lean_closure_set(x_124, 0, x_118);
lean_closure_set(x_124, 1, x_119);
lean_closure_set(x_124, 2, x_123);
lean_ctor_set(x_121, 0, x_124);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 8, 3);
lean_closure_set(x_127, 0, x_118);
lean_closure_set(x_127, 1, x_119);
lean_closure_set(x_127, 2, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_119);
lean_dec(x_118);
x_129 = !lean_is_exclusive(x_121);
if (x_129 == 0)
{
return x_121;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_121, 0);
x_131 = lean_ctor_get(x_121, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_121);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 5:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
lean_dec(x_1);
x_134 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5), 6, 1);
lean_closure_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_4);
return x_135;
}
case 6:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
lean_dec(x_1);
x_137 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6), 6, 1);
lean_closure_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_4);
return x_138;
}
case 7:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
lean_dec(x_1);
x_140 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7), 6, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_4);
return x_141;
}
case 8:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
lean_dec(x_1);
x_143 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
x_144 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(x_143, x_142, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_144;
}
case 9:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_1, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 2);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_pretty_printer_formatter_interpret_parser_descr(x_146, x_2, x_3, x_4);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_150, 0, x_145);
lean_closure_set(x_150, 1, x_149);
lean_ctor_set(x_147, 0, x_150);
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_147);
x_153 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_153, 0, x_145);
lean_closure_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_145);
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
return x_147;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_147, 0);
x_157 = lean_ctor_get(x_147, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_147);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
case 10:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_163 = lean_pretty_printer_formatter_interpret_parser_descr(x_159, x_2, x_3, x_4);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_pretty_printer_formatter_interpret_parser_descr(x_161, x_2, x_3, x_165);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_box(x_162);
x_170 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9___boxed), 9, 4);
lean_closure_set(x_170, 0, x_160);
lean_closure_set(x_170, 1, x_169);
lean_closure_set(x_170, 2, x_164);
lean_closure_set(x_170, 3, x_168);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_166, 0);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_166);
x_173 = lean_box(x_162);
x_174 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9___boxed), 9, 4);
lean_closure_set(x_174, 0, x_160);
lean_closure_set(x_174, 1, x_173);
lean_closure_set(x_174, 2, x_164);
lean_closure_set(x_174, 3, x_171);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_164);
lean_dec(x_160);
x_176 = !lean_is_exclusive(x_166);
if (x_176 == 0)
{
return x_166;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_166, 0);
x_178 = lean_ctor_get(x_166, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_166);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_163);
if (x_180 == 0)
{
return x_163;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_163, 0);
x_182 = lean_ctor_get(x_163, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_163);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 2);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_188 = lean_pretty_printer_formatter_interpret_parser_descr(x_184, x_2, x_3, x_4);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_pretty_printer_formatter_interpret_parser_descr(x_186, x_2, x_3, x_190);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_box(x_187);
x_195 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10___boxed), 9, 4);
lean_closure_set(x_195, 0, x_185);
lean_closure_set(x_195, 1, x_194);
lean_closure_set(x_195, 2, x_189);
lean_closure_set(x_195, 3, x_193);
lean_ctor_set(x_191, 0, x_195);
return x_191;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_191, 0);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_191);
x_198 = lean_box(x_187);
x_199 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10___boxed), 9, 4);
lean_closure_set(x_199, 0, x_185);
lean_closure_set(x_199, 1, x_198);
lean_closure_set(x_199, 2, x_189);
lean_closure_set(x_199, 3, x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
uint8_t x_201; 
lean_dec(x_189);
lean_dec(x_185);
x_201 = !lean_is_exclusive(x_191);
if (x_201 == 0)
{
return x_191;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_191, 0);
x_203 = lean_ctor_get(x_191, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_191);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
return x_188;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_188);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Parser_Level(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Parser_Tactic(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_Parser_Module(lean_object*);
lean_object* initialize_Lean_Parser_Syntax(lean_object*);
lean_object* initialize_Lean_Parser_Do(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35);
res = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
