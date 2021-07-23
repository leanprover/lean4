// Lean compiler output
// Module: Lean.Parser.Extra
// Imports: Init Lean.Parser.Extension Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter
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
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many___closed__3;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__17;
lean_object* l_Lean_PrettyPrinter_Formatter_indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit___closed__1;
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_72____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54;
static lean_object* l_Lean_Parser_numLit___elambda__1___closed__2;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__14;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_Parser_optional___closed__1;
static lean_object* l_Lean_Parser_commandParser_formatter___rarg___closed__2;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25;
static lean_object* l_Lean_Parser_commandParser_formatter___rarg___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__5;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__10;
lean_object* l_Lean_ppHardSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_ppHardSpace___closed__1;
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__6;
static lean_object* l_Lean_Parser_ppHardSpace___closed__2;
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__10;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit___closed__4;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52;
static lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_many1Indent_parenthesizer___closed__1;
lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__3;
lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46;
lean_object* l_Lean_Parser_ppGroup___boxed(lean_object*);
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__4;
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__15;
static lean_object* l_Lean_Parser_numLit___elambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many___closed__5;
static lean_object* l_Lean_Parser_ident_formatter___closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36;
lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31;
lean_object* l_Lean_PrettyPrinter_Formatter_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit_formatter___closed__3;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__8;
static lean_object* l_Lean_Parser_ident_formatter___closed__2;
static lean_object* l_Lean_Parser_many___closed__2;
lean_object* l_Lean_Parser_scientificLit;
lean_object* l_Lean_ppSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6;
lean_object* l_Lean_Parser_tokenWithAntiquotFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group(lean_object*);
lean_object* l_Lean_Parser_ident;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__13;
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__3;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26;
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLit___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit_formatter___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41;
lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_optional_formatter___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__9;
static lean_object* l_Lean_Parser_strLit_formatter___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42;
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__2;
static lean_object* l_Lean_Parser_charLit___elambda__1___closed__1;
lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37;
static lean_object* l_Lean_Parser_numLit___closed__3;
static lean_object* l_Lean_Parser_optional_formatter___closed__2;
static lean_object* l_Lean_Parser_charLit___elambda__1___closed__2;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_631____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5;
lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__14;
static lean_object* l_Lean_Parser_scientificLit___closed__4;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__5;
lean_object* l_Lean_Parser_checkColGeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__4;
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine;
extern lean_object* l_Lean_nameLitKind;
static lean_object* l_Lean_Parser_strLit___closed__1;
lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13;
static lean_object* l_Lean_Parser_strLit_formatter___closed__3;
static lean_object* l_Lean_Parser_leadingNode_formatter___closed__1;
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43;
static lean_object* l_Lean_Parser_ident___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawIdent___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
static lean_object* l_Lean_Parser_numLit___closed__1;
lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16;
lean_object* l_Lean_ppIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*);
static lean_object* l_Lean_Parser_ident_formatter___closed__3;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20;
static lean_object* l_Lean_Parser_numLit___closed__2;
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ident___closed__4;
lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1;
static lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_ident___closed__2;
lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__7;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__12;
static lean_object* l_Lean_Parser_charLit_formatter___closed__2;
lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19;
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit_parenthesizer___closed__2;
lean_object* l_Lean_Parser_termRegister__parser__alias______;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawIdent___closed__4;
extern lean_object* l_Lean_numLitKind;
static lean_object* l_Lean_Parser_strLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit_formatter___closed__4;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__9;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit_formatter___closed__3;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
static lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2;
lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_decQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45;
lean_object* l_Lean_Parser_manyIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit_formatter___closed__1;
static lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__1;
lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27;
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit___closed__3;
static lean_object* l_Lean_Parser_many___closed__1;
lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2;
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
static lean_object* l_Lean_Parser_strLit___elambda__1___closed__2;
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39;
static lean_object* l_Lean_Parser_many1Indent_formatter___closed__1;
lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit_formatter___closed__4;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__6;
lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9;
static lean_object* l_Lean_Parser_charLit___closed__3;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Parser_many1___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyIndent(lean_object*);
static lean_object* l_Lean_Parser_nameLit___closed__1;
lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit_formatter___closed__4;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53;
lean_object* l_Lean_Parser_ppSpace;
static lean_object* l_Lean_Parser_optional___closed__5;
lean_object* l_Lean_Parser_ppHardSpace;
extern lean_object* l_Lean_Parser_parserAliasesRef;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit___closed__2;
lean_object* l_Lean_Parser_termParser_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__2;
lean_object* l_Lean_Parser_ppIndent(lean_object*);
lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55;
extern lean_object* l_Lean_charLitKind;
static lean_object* l_Lean_Parser_nameLit___closed__4;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32;
static lean_object* l_Lean_Parser_optional___closed__3;
static lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__2;
lean_object* l_Lean_Parser_ppDedent(lean_object*);
static lean_object* l_Lean_Parser_strLit___elambda__1___closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10;
static lean_object* l_Lean_Parser_rawIdent___closed__5;
lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3;
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__10;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__16;
static lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_optional_formatter___closed__3;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__8;
static lean_object* l_Lean_Parser_rawIdent___elambda__1___closed__1;
static lean_object* l_Lean_Parser_numLit_formatter___closed__3;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44;
static lean_object* l_Lean_Parser_scientificLit___closed__3;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__9;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8;
static lean_object* l_Lean_Parser_numLit_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31;
static lean_object* l_Lean_ppHardSpace_formatter___closed__2;
lean_object* l_Lean_Parser_ppIndent___boxed(lean_object*);
static lean_object* l_Lean_Parser_optional_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__11;
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_formatter(lean_object*);
static lean_object* l_Lean_Parser_rawIdent_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_strLit___closed__3;
lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit___closed__4;
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6;
static lean_object* l_Lean_ppHardSpace_formatter___closed__1;
static lean_object* l_Lean_Parser_numLit_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawIdent___closed__2;
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__6;
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41;
lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit___elambda__1___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22;
lean_object* l_Lean_Parser_notSymbol(lean_object*);
lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6;
lean_object* l_Lean_Parser_termParser_formatter(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_groupKind;
static lean_object* l_Lean_Parser_ident___elambda__1___closed__1;
lean_object* l_Lean_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__1;
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Parser_commandParser_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many_formatter___closed__3;
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25;
static lean_object* l_Lean_Parser_nameLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit;
static lean_object* l_Lean_Parser_many___closed__4;
static lean_object* l_Lean_Parser_charLit_formatter___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46;
lean_object* l_Lean_Parser_ppHardSpace___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppDedent___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486_(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
extern lean_object* l_Lean_scientificLitKind;
static lean_object* l_Lean_Parser_scientificLit___elambda__1___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*);
static lean_object* l_Lean_Parser_termParser_formatter___rarg___closed__2;
lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__16;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit___elambda__1___closed__2;
static lean_object* l_Lean_Parser_termParser_formatter___rarg___closed__1;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__10;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35;
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__7;
static lean_object* l_Lean_Parser_nameLit_parenthesizer___closed__2;
lean_object* l_Lean_Parser_many___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__6;
static lean_object* l_Lean_Parser_charLit_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_charLit_formatter___closed__3;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__11;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36;
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_optional___closed__2;
lean_object* l_Lean_Parser_many1Indent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ppDedent_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*);
lean_object* l_Std_Format_getIndent(lean_object*);
static lean_object* l_Lean_Parser_ident___elambda__1___closed__2;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14;
lean_object* l_Lean_Parser_notSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__9;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__2;
lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit_formatter___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30;
lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_optional_formatter___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5;
lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit_formatter___closed__2;
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47;
lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4;
static lean_object* l_Lean_Parser_scientificLit_formatter___closed__4;
lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many_formatter___closed__2;
lean_object* l_Lean_Parser_nameLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8;
lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit_formatter___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40;
static lean_object* l_Lean_Parser_rawIdent___closed__1;
static lean_object* l_Lean_Parser_many_formatter___closed__1;
static lean_object* l_Lean_Parser_scientificLit_formatter___closed__2;
static lean_object* l_Lean_Parser_strLit___closed__4;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15;
static lean_object* l_Lean_ppLine_formatter___closed__1;
static lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__4;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__13;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit_formatter___closed__2;
lean_object* l_Lean_Parser_ppGroup(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__4;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20;
static lean_object* l_Lean_Parser_ident_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_optional___closed__4;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_ppLine_formatter___closed__2;
static lean_object* l_Lean_Parser_rawIdent_formatter___closed__1;
lean_object* l_Lean_Parser_ppHardSpace___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__12;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32;
lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10;
lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27;
lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16;
static lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__8;
lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ident___closed__3;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__5;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24;
static lean_object* l_Lean_Parser_nameLit_formatter___closed__4;
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit___closed__2;
static lean_object* l_Lean_Parser_many1Indent___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48;
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Parser_scientificLit_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__7;
static lean_object* l_Lean_Parser_nameLit___elambda__1___closed__2;
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_termRegister__parser__alias_________closed__15;
lean_object* l_Lean_Parser_notSymbol_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Parser_rawIdent___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit___closed__1;
lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit___closed__2;
lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notSymbol_formatter___rarg(lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__1;
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47;
static lean_object* l_Lean_Parser_leadingNode_formatter___closed__2;
lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
lean_object* l_Lean_ppDedent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many1Indent___closed__2;
static lean_object* _init_l_Lean_Parser_leadingNode_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_leadingNode_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_leadingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_leadingNode_formatter___closed__2;
x_13 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_12, x_11, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_leadingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_termParser_formatter___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termParser_formatter___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termParser_formatter___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_termParser_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_termParser_formatter___rarg___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_termParser_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_termParser_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_termParser_formatter___rarg___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_commandParser_formatter___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_commandParser_formatter___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_commandParser_formatter___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_commandParser_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_commandParser_formatter___rarg___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_commandParser_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_commandParser_formatter___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_commandParser_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_commandParser_formatter___rarg___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_symbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotNestedExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___rarg), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_decQuotDepth_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__6;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__8;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__4;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__9;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_7 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__10;
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_antiquotExpr_formatter___closed__1;
x_7 = l_Lean_Parser_antiquotExpr_formatter___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_formatter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__6;
x_2 = l_Lean_Parser_mkAntiquot_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotName");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot_formatter___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__11;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_formatter___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__14;
x_2 = l_Lean_Parser_mkAntiquot_formatter___closed__15;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_9 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
x_9 = x_54;
goto block_52;
}
block_52:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_mkAntiquot_formatter___closed__2;
x_11 = l_Lean_Name_append(x_9, x_10);
lean_dec(x_9);
if (x_3 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_mkAntiquot_formatter___closed__12;
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_mkAntiquot_formatter___closed__6;
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_mkAntiquot_formatter___closed__10;
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_mkAntiquot_formatter___closed__13;
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_mkAntiquot_formatter___closed__8;
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_mkAntiquot_formatter___closed__5;
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_atomic_formatter), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Parser_maxPrec;
x_30 = l_Lean_Parser_leadingNode_formatter(x_11, x_29, x_28, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_32);
x_34 = l_Lean_Parser_mkAntiquot_formatter___closed__12;
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_mkAntiquot_formatter___closed__6;
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_mkAntiquot_formatter___closed__10;
x_39 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_37);
x_40 = l_Lean_Parser_mkAntiquot_formatter___closed__16;
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
x_42 = l_Lean_Parser_mkAntiquot_formatter___closed__13;
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_44, 0, x_36);
lean_closure_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_mkAntiquot_formatter___closed__8;
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_44);
x_47 = l_Lean_Parser_mkAntiquot_formatter___closed__5;
x_48 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_46);
x_49 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_atomic_formatter), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = l_Lean_Parser_maxPrec;
x_51 = l_Lean_Parser_leadingNode_formatter(x_11, x_50, x_49, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_7 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
x_7 = l_Lean_Parser_antiquotExpr_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
x_2 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_formatter___closed__11;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_parenthesizer), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__8;
x_2 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__9;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_9 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
x_9 = x_54;
goto block_52;
}
block_52:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_mkAntiquot_formatter___closed__2;
x_11 = l_Lean_Name_append(x_9, x_10);
lean_dec(x_9);
if (x_3 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__6;
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_mkAntiquot_formatter___closed__10;
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__7;
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__5;
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__2;
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Parser_maxPrec;
x_30 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_11, x_29, x_28, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_32);
x_34 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__6;
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_mkAntiquot_formatter___closed__10;
x_39 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_37);
x_40 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__10;
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
x_42 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__7;
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_44, 0, x_36);
lean_closure_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__5;
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_44);
x_47 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__2;
x_48 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_46);
x_49 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = l_Lean_Parser_maxPrec;
x_51 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_11, x_50, x_49, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Parser_mkAntiquot_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
x_14 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_scope");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__2;
x_10 = l_Lean_Name_append(x_1, x_9);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__6;
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__4;
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_mkAntiquot_formatter___closed__6;
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
x_20 = l_Lean_Parser_mkAntiquot_formatter___closed__8;
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_mkAntiquot_formatter___closed__5;
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_atomic_formatter), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_maxPrec;
x_26 = l_Lean_Parser_leadingNode_formatter(x_10, x_25, x_24, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquotSplice_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_formatter___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg), 7, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_sepByElemParser_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("*");
return x_1;
}
}
lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_String_trim(x_2);
x_9 = l_Lean_Parser_sepByElemParser_formatter___closed__3;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_sepByElemParser_formatter___closed__2;
x_13 = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(x_12, x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Parser_sepBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = l_Lean_Parser_mkAntiquotSplice_formatter___closed__2;
x_10 = l_Lean_Name_append(x_1, x_9);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2;
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1;
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
x_20 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__5;
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__2;
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_maxPrec;
x_26 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_10, x_25, x_24, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquotSplice_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg), 7, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_String_trim(x_2);
x_9 = l_Lean_Parser_sepByElemParser_formatter___closed__3;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_sepByElemParser_formatter___closed__2;
x_13 = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(x_12, x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy1_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy1_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_optional_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optional");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_optional_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_optional_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_optional_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_optional_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_optional_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_optional_formatter___closed__2;
x_8 = l_Lean_Parser_optional_formatter___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_optional_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_optional_formatter___closed__2;
x_8 = l_Lean_Parser_optional_parenthesizer___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_optional___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_optionalFn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional_formatter___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional___closed__1;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_optional___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_optional___closed__2;
x_2 = l_Lean_Parser_optional___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_optional(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_Parser_optional_formatter___closed__2;
x_3 = l_Lean_Parser_optional___closed__5;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_optionaInfo(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_optional___elambda__1), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_many_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("many");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_many_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_many_formatter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_many_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_sepByElemParser_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_many_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many_formatter___closed__2;
x_8 = l_Lean_Parser_many_formatter___closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_many_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_sepByElemParser_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_many_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many_formatter___closed__2;
x_8 = l_Lean_Parser_many_parenthesizer___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_many___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_manyAux(x_1, x_2, x_3);
x_7 = l_Lean_nullKind;
x_8 = l_Lean_Parser_ParserState_mkNode(x_6, x_7, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_sepByElemParser_formatter___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_many___closed__1;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_many___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_many___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_many___closed__2;
x_2 = l_Lean_Parser_many___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_many(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_Parser_many_formatter___closed__2;
x_3 = l_Lean_Parser_many___closed__5;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_noFirstTokenInfo(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_many___elambda__1), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_many1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many_formatter___closed__2;
x_8 = l_Lean_Parser_many_formatter___closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many_formatter___closed__2;
x_8 = l_Lean_Parser_many_parenthesizer___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_many1___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_631____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_6, x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_manyAux(x_1, x_2, x_6);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_5);
return x_14;
}
}
}
lean_object* l_Lean_Parser_many1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Parser_many_formatter___closed__2;
x_3 = l_Lean_Parser_many___closed__5;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_many1___elambda__1), 3, 1);
lean_closure_set(x_7, 0, x_6);
lean_ctor_set(x_4, 1, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_many1___elambda__1), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Parser_ident_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_identKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ident_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ident_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_ident_formatter___closed__2;
x_2 = l_Lean_Parser_ident_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_formatter___closed__3;
x_7 = l_Lean_Parser_antiquotExpr_formatter___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_ident_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_ident_formatter___closed__2;
x_2 = l_Lean_Parser_ident_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_parenthesizer___closed__1;
x_7 = l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_ident___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident_formatter___closed__2;
x_2 = l_Lean_Parser_ident_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_ident___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_ident___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_ident___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_identFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_ident___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_ident___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_ident___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ident() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ident___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_rawIdent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_formatter___closed__3;
x_7 = l_Lean_Parser_rawIdent_formatter___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_parenthesizer___closed__1;
x_7 = l_Lean_Parser_rawIdent_parenthesizer___closed__1;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdentFn___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_rawIdent___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_ident___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_rawIdentFn(x_1, x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_rawIdent___elambda__1___closed__1;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_rawIdent___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_rawIdent___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdent___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_rawIdent___closed__3;
x_2 = l_Lean_Parser_rawIdent___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_rawIdent___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLit_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLit_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLit_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_numLit_formatter___closed__2;
x_2 = l_Lean_Parser_numLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_numLit_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_numLit_formatter___closed__3;
x_7 = l_Lean_Parser_numLit_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_numLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_numLit_formatter___closed__2;
x_2 = l_Lean_Parser_numLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_numLit_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_numLit_parenthesizer___closed__1;
x_7 = l_Lean_Parser_numLit_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_numLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_numLit_formatter___closed__2;
x_2 = l_Lean_Parser_numLit_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_numLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_numLit___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_numLit___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_numLitFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_numLit___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLit_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_numLit___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_numLit___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_numLit___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_numLit___closed__2;
x_2 = l_Lean_Parser_numLit___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_numLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_numLit___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_scientificLitKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scientificLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_scientificLit_formatter___closed__2;
x_2 = l_Lean_Parser_scientificLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_scientificLit_formatter___closed__3;
x_7 = l_Lean_Parser_scientificLit_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_scientificLit_formatter___closed__2;
x_2 = l_Lean_Parser_scientificLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_scientificLit_parenthesizer___closed__1;
x_7 = l_Lean_Parser_scientificLit_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_scientificLit_formatter___closed__2;
x_2 = l_Lean_Parser_scientificLit_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_scientificLit___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_scientificLit___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_scientificLitFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_scientificLit___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_scientificLit_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_scientificLit___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_scientificLit___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLit___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_scientificLit___closed__2;
x_2 = l_Lean_Parser_scientificLit___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_scientificLit___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLit_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_strLit_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLit_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_strLit_formatter___closed__2;
x_2 = l_Lean_Parser_strLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_strLit_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_strLit_formatter___closed__3;
x_7 = l_Lean_Parser_strLit_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_strLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_strLit_formatter___closed__2;
x_2 = l_Lean_Parser_strLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_strLit_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_strLit_parenthesizer___closed__1;
x_7 = l_Lean_Parser_strLit_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_strLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_strLit_formatter___closed__2;
x_2 = l_Lean_Parser_strLit_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_strLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_strLit___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_strLit___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_strLitFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_strLit___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLit_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_strLit___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_strLit___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_strLit___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_strLit___closed__2;
x_2 = l_Lean_Parser_strLit___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_strLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_strLit___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLit_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_charLit_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("charLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLit_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_charLit_formatter___closed__2;
x_2 = l_Lean_Parser_charLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_charLit_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_charLit_formatter___closed__3;
x_7 = l_Lean_Parser_charLit_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_charLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_charLit_formatter___closed__2;
x_2 = l_Lean_Parser_charLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_charLit_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_charLit_parenthesizer___closed__1;
x_7 = l_Lean_Parser_charLit_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_charLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_charLit_formatter___closed__2;
x_2 = l_Lean_Parser_charLit_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_charLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_charLit___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_charLit___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_charLitFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_charLit___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLit_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_charLit___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_charLit___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_charLit___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_charLit___closed__2;
x_2 = l_Lean_Parser_charLit___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_charLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_charLit___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameLitKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nameLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_nameLit_formatter___closed__2;
x_2 = l_Lean_Parser_nameLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_nameLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_nameLit_formatter___closed__3;
x_7 = l_Lean_Parser_nameLit_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_nameLit_formatter___closed__2;
x_2 = l_Lean_Parser_nameLit_formatter___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_nameLit_parenthesizer___closed__1;
x_7 = l_Lean_Parser_nameLit_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_nameLit_formatter___closed__2;
x_2 = l_Lean_Parser_nameLit_formatter___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_nameLit___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_nameLit___elambda__1___closed__1;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Parser_nameLitFn(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_nameLit___elambda__1___closed__2;
x_8 = 1;
x_9 = l_Lean_Parser_orelseFnCore(x_4, x_7, x_8, x_1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLit_formatter___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_nameLit___elambda__1___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_nameLit___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nameLit___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_nameLit___closed__2;
x_2 = l_Lean_Parser_nameLit___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_nameLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_nameLit___closed__4;
return x_1;
}
}
lean_object* l_Lean_Parser_group_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_groupKind;
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_group_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_groupKind;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_group(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_groupKind;
x_4 = l_Lean_Parser_nodeInfo(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_many1Indent_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_many1Indent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_many1Indent_formatter___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many1_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_many1Indent_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many1Indent_parenthesizer___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_many1Indent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 5);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_2, 5, x_13);
x_14 = lean_apply_2(x_5, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_2, 5, x_21);
lean_ctor_set(x_2, 1, x_19);
x_22 = lean_apply_2(x_5, x_2, x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 3);
lean_inc(x_30);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_31 = x_7;
} else {
 lean_dec_ref(x_7);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 4, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_2, 5, x_34);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_26);
x_35 = lean_apply_2(x_5, x_2, x_3);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
x_39 = lean_ctor_get(x_2, 4);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_41 = lean_ctor_get(x_2, 6);
lean_inc(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 3);
lean_inc(x_50);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 x_51 = x_36;
} else {
 lean_dec_ref(x_36);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_38);
lean_ctor_set(x_55, 4, x_39);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*7, x_40);
x_56 = lean_apply_2(x_5, x_55, x_3);
return x_56;
}
}
}
static lean_object* _init_l_Lean_Parser_many1Indent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("irrelevant");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_many1Indent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_many1Indent___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_many1Indent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_rawIdent___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Parser_many1Indent___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_many1(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent___lambda__1), 3, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_ctor_set(x_9, 1, x_11);
return x_9;
}
else
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
lean_object* l_Lean_Parser_manyIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_many1Indent_formatter___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_many1Indent_parenthesizer___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_manyIndent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_rawIdent___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Parser_many1Indent___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_many(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent___lambda__1), 3, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_ctor_set(x_9, 1, x_11);
return x_9;
}
else
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
lean_object* l_Lean_Parser_notSymbol_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_notSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_notSymbol_formatter___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_notSymbol_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_notSymbol_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_notSymbol_parenthesizer___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_notSymbol_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_notSymbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_String_trim(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Lean_Parser_rawIdent___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_ppHardSpace___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppHardSpace___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_ppHardSpace___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ppHardSpace___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_ppHardSpace___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ppHardSpace___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ppSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ppHardSpace___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ppLine() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ppHardSpace___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_ppGroup(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ppGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppGroup(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ppIndent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ppIndent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppIndent(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ppDedent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ppDedent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedent(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ppHardSpace_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l_Lean_ppHardSpace_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppHardSpace_formatter___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppHardSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_ppHardSpace_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_push(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardSpace_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ppSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ppSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppSpace_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_ppLine_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Lean_ppLine_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppLine_formatter___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppLine_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_ppLine_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_push(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_ppLine_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppLine_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ppGroup_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_indent___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_group(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_ppIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_ppDedent_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Lean_ppDedent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Std_Format_getIndent(x_7);
lean_dec(x_7);
x_9 = lean_nat_to_int(x_8);
x_10 = l_Lean_ppDedent_formatter___closed__1;
x_11 = lean_int_sub(x_10, x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_12);
return x_13;
}
}
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_ppHardSpace_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ppHardSpace_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_ppSpace_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_ppSpace_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ppSpace_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_ppLine_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_ppLine_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ppLine_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__2;
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termRegister_parser_alias___");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__4;
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("register_parser_alias");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__4;
x_2 = l_Lean_Parser_strLit_formatter___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__11;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__8;
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__10;
x_3 = l_Lean_Parser_termRegister__parser__alias_________closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__4;
x_2 = l_Lean_Parser_ident_formatter___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__14;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__8;
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__13;
x_3 = l_Lean_Parser_termRegister__parser__alias_________closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_________closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_termRegister__parser__alias_________closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias______() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__17;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__4;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("do");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqIndent");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqItem");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser.registerAlias");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termRegister__parser__alias_________closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("registerAlias");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__4;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter.Formatter.registerAlias");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termRegister__parser__alias_________closed__2;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter.Parenthesizer.registerAlias");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49;
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_termRegister__parser__alias_________closed__6;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_72____spec__1(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3;
lean_inc(x_14);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20;
lean_inc(x_15);
lean_inc(x_16);
x_20 = l_Lean_addMacroScope(x_16, x_19, x_15);
x_21 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17;
x_22 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23;
lean_inc(x_14);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24;
x_25 = lean_array_push(x_24, x_9);
lean_inc(x_11);
lean_inc(x_25);
x_26 = lean_array_push(x_25, x_11);
x_27 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_24, x_23);
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_24, x_36);
x_38 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27;
x_39 = lean_array_push(x_37, x_38);
x_40 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35;
lean_inc(x_15);
lean_inc(x_16);
x_43 = l_Lean_addMacroScope(x_16, x_42, x_15);
x_44 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30;
x_45 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40;
lean_inc(x_14);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Lean_Syntax_getId(x_11);
x_48 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42;
x_49 = l_Lean_Name_append(x_47, x_48);
x_50 = l_Lean_mkIdentFrom(x_11, x_49);
lean_inc(x_25);
x_51 = lean_array_push(x_25, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_24, x_46);
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_push(x_33, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_35);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_24, x_57);
x_59 = lean_array_push(x_58, x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_40);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48;
x_62 = l_Lean_addMacroScope(x_16, x_61, x_15);
x_63 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45;
x_64 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52;
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
x_66 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54;
x_67 = l_Lean_Name_append(x_47, x_66);
lean_dec(x_47);
x_68 = l_Lean_mkIdentFrom(x_11, x_67);
lean_dec(x_11);
x_69 = lean_array_push(x_25, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_24, x_65);
x_72 = lean_array_push(x_71, x_70);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_31);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_33, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_24, x_75);
x_77 = lean_array_push(x_76, x_38);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55;
x_80 = lean_array_push(x_79, x_41);
x_81 = lean_array_push(x_80, x_60);
x_82 = lean_array_push(x_81, x_78);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_27);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_33, x_83);
x_85 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_24, x_18);
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_12, 0, x_90);
return x_12;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_91 = lean_ctor_get(x_12, 0);
x_92 = lean_ctor_get(x_12, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_12);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
lean_dec(x_2);
x_95 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3;
lean_inc(x_91);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20;
lean_inc(x_93);
lean_inc(x_94);
x_98 = l_Lean_addMacroScope(x_94, x_97, x_93);
x_99 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17;
x_100 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23;
lean_inc(x_91);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
x_102 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24;
x_103 = lean_array_push(x_102, x_9);
lean_inc(x_11);
lean_inc(x_103);
x_104 = lean_array_push(x_103, x_11);
x_105 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_array_push(x_102, x_101);
x_108 = lean_array_push(x_107, x_106);
x_109 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25;
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_102, x_114);
x_116 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27;
x_117 = lean_array_push(x_115, x_116);
x_118 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35;
lean_inc(x_93);
lean_inc(x_94);
x_121 = l_Lean_addMacroScope(x_94, x_120, x_93);
x_122 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30;
x_123 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40;
lean_inc(x_91);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_91);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_123);
x_125 = l_Lean_Syntax_getId(x_11);
x_126 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42;
x_127 = l_Lean_Name_append(x_125, x_126);
x_128 = l_Lean_mkIdentFrom(x_11, x_127);
lean_inc(x_103);
x_129 = lean_array_push(x_103, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_push(x_102, x_124);
x_132 = lean_array_push(x_131, x_130);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_109);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_push(x_111, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_102, x_135);
x_137 = lean_array_push(x_136, x_116);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_118);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48;
x_140 = l_Lean_addMacroScope(x_94, x_139, x_93);
x_141 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45;
x_142 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52;
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_91);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_142);
x_144 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54;
x_145 = l_Lean_Name_append(x_125, x_144);
lean_dec(x_125);
x_146 = l_Lean_mkIdentFrom(x_11, x_145);
lean_dec(x_11);
x_147 = lean_array_push(x_103, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_105);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_push(x_102, x_143);
x_150 = lean_array_push(x_149, x_148);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_109);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_111, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_113);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_push(x_102, x_153);
x_155 = lean_array_push(x_154, x_116);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_118);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55;
x_158 = lean_array_push(x_157, x_119);
x_159 = lean_array_push(x_158, x_138);
x_160 = lean_array_push(x_159, x_156);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_105);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_array_push(x_111, x_161);
x_163 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_array_push(x_102, x_96);
x_166 = lean_array_push(x_165, x_164);
x_167 = l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_92);
return x_169;
}
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_group), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_group_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppHardSpace");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ppHardSpace___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppHardSpace_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppHardSpace_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppSpace");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppSpace_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppSpace_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppLine");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppLine_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppGroup");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppGroup_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppIndent");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppIndent___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppIndent_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppDedent");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppDedent___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ppDedent_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_parserAliasesRef;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2;
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_8 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_3, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_12 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_3, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10;
x_16 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11;
x_17 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_15, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13;
x_20 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_15, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15;
x_23 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_15, x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17;
x_26 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_25, x_16, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19;
x_29 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_25, x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21;
x_32 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_25, x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23;
x_35 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_34, x_16, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25;
x_38 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_34, x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27;
x_41 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_34, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29;
x_44 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31;
x_45 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_43, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33;
x_48 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_43, x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35;
x_51 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_43, x_50, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37;
x_54 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39;
x_55 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_53, x_54, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41;
x_58 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_53, x_57, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43;
x_61 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_53, x_60, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45;
x_64 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47;
x_65 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_63, x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49;
x_68 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_63, x_67, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51;
x_71 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_63, x_70, x_69);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_65);
if (x_76 == 0)
{
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
x_78 = lean_ctor_get(x_65, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_65);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
return x_61;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_61, 0);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_58);
if (x_84 == 0)
{
return x_58;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_58, 0);
x_86 = lean_ctor_get(x_58, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_58);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_55);
if (x_88 == 0)
{
return x_55;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_55, 0);
x_90 = lean_ctor_get(x_55, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_55);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_51);
if (x_92 == 0)
{
return x_51;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_51, 0);
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_51);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_48);
if (x_96 == 0)
{
return x_48;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_48, 0);
x_98 = lean_ctor_get(x_48, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_48);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
return x_45;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_45, 0);
x_102 = lean_ctor_get(x_45, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_45);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_41);
if (x_104 == 0)
{
return x_41;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_41, 0);
x_106 = lean_ctor_get(x_41, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_41);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_38);
if (x_108 == 0)
{
return x_38;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_38, 0);
x_110 = lean_ctor_get(x_38, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_38);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_35);
if (x_112 == 0)
{
return x_35;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_35, 0);
x_114 = lean_ctor_get(x_35, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_35);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_32);
if (x_116 == 0)
{
return x_32;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_32, 0);
x_118 = lean_ctor_get(x_32, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_32);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_29);
if (x_120 == 0)
{
return x_29;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_29, 0);
x_122 = lean_ctor_get(x_29, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_29);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_26);
if (x_124 == 0)
{
return x_26;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_26, 0);
x_126 = lean_ctor_get(x_26, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_26);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_23);
if (x_128 == 0)
{
return x_23;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_23, 0);
x_130 = lean_ctor_get(x_23, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_23);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_20);
if (x_132 == 0)
{
return x_20;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_20, 0);
x_134 = lean_ctor_get(x_20, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_20);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_17);
if (x_136 == 0)
{
return x_17;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_17, 0);
x_138 = lean_ctor_get(x_17, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_17);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_13);
if (x_140 == 0)
{
return x_13;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_13, 0);
x_142 = lean_ctor_get(x_13, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_13);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_9);
if (x_144 == 0)
{
return x_9;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_9, 0);
x_146 = lean_ctor_get(x_9, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_9);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_5);
if (x_148 == 0)
{
return x_5;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_5, 0);
x_150 = lean_ctor_get(x_5, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_5);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Extra(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_leadingNode_formatter___closed__1 = _init_l_Lean_Parser_leadingNode_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_leadingNode_formatter___closed__1);
l_Lean_Parser_leadingNode_formatter___closed__2 = _init_l_Lean_Parser_leadingNode_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_leadingNode_formatter___closed__2);
l_Lean_Parser_termParser_formatter___rarg___closed__1 = _init_l_Lean_Parser_termParser_formatter___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_termParser_formatter___rarg___closed__1);
l_Lean_Parser_termParser_formatter___rarg___closed__2 = _init_l_Lean_Parser_termParser_formatter___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_termParser_formatter___rarg___closed__2);
l_Lean_Parser_commandParser_formatter___rarg___closed__1 = _init_l_Lean_Parser_commandParser_formatter___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_commandParser_formatter___rarg___closed__1);
l_Lean_Parser_commandParser_formatter___rarg___closed__2 = _init_l_Lean_Parser_commandParser_formatter___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_commandParser_formatter___rarg___closed__2);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__1 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__1);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__2 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__3 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__4 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__4);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__5 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__6 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__6);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__7 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__7);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__8 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__8);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__9 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__9);
l_Lean_Parser_antiquotNestedExpr_formatter___closed__10 = _init_l_Lean_Parser_antiquotNestedExpr_formatter___closed__10();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_formatter___closed__10);
l_Lean_Parser_antiquotExpr_formatter___closed__1 = _init_l_Lean_Parser_antiquotExpr_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_formatter___closed__1);
l_Lean_Parser_antiquotExpr_formatter___closed__2 = _init_l_Lean_Parser_antiquotExpr_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_formatter___closed__2);
l_Lean_Parser_mkAntiquot_formatter___closed__1 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__1);
l_Lean_Parser_mkAntiquot_formatter___closed__2 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__2);
l_Lean_Parser_mkAntiquot_formatter___closed__3 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__3);
l_Lean_Parser_mkAntiquot_formatter___closed__4 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__4);
l_Lean_Parser_mkAntiquot_formatter___closed__5 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__5);
l_Lean_Parser_mkAntiquot_formatter___closed__6 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__6);
l_Lean_Parser_mkAntiquot_formatter___closed__7 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__7);
l_Lean_Parser_mkAntiquot_formatter___closed__8 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__8);
l_Lean_Parser_mkAntiquot_formatter___closed__9 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__9);
l_Lean_Parser_mkAntiquot_formatter___closed__10 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__10();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__10);
l_Lean_Parser_mkAntiquot_formatter___closed__11 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__11();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__11);
l_Lean_Parser_mkAntiquot_formatter___closed__12 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__12();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__12);
l_Lean_Parser_mkAntiquot_formatter___closed__13 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__13();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__13);
l_Lean_Parser_mkAntiquot_formatter___closed__14 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__14();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__14);
l_Lean_Parser_mkAntiquot_formatter___closed__15 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__15();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__15);
l_Lean_Parser_mkAntiquot_formatter___closed__16 = _init_l_Lean_Parser_mkAntiquot_formatter___closed__16();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_formatter___closed__16);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__5);
l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6 = _init_l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__6);
l_Lean_Parser_antiquotExpr_parenthesizer___closed__1 = _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_parenthesizer___closed__1);
l_Lean_Parser_antiquotExpr_parenthesizer___closed__2 = _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_parenthesizer___closed__2);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__1 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__2 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__2);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__3 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__3);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__4 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__4);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__5 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__5);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__6 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__6);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__7 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__7);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__8 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__8);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__9 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__9();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__9);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__10 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__10();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__10);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__1 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__2 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__2);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__3 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__3);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__4 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__4);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__5 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5);
l_Lean_Parser_mkAntiquotSplice_formatter___closed__6 = _init_l_Lean_Parser_mkAntiquotSplice_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_formatter___closed__6);
l_Lean_Parser_sepByElemParser_formatter___closed__1 = _init_l_Lean_Parser_sepByElemParser_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_sepByElemParser_formatter___closed__1);
l_Lean_Parser_sepByElemParser_formatter___closed__2 = _init_l_Lean_Parser_sepByElemParser_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_sepByElemParser_formatter___closed__2);
l_Lean_Parser_sepByElemParser_formatter___closed__3 = _init_l_Lean_Parser_sepByElemParser_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_sepByElemParser_formatter___closed__3);
l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1 = _init_l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1);
l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2 = _init_l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__2);
l_Lean_Parser_optional_formatter___closed__1 = _init_l_Lean_Parser_optional_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_optional_formatter___closed__1);
l_Lean_Parser_optional_formatter___closed__2 = _init_l_Lean_Parser_optional_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_optional_formatter___closed__2);
l_Lean_Parser_optional_formatter___closed__3 = _init_l_Lean_Parser_optional_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_optional_formatter___closed__3);
l_Lean_Parser_optional_formatter___closed__4 = _init_l_Lean_Parser_optional_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_optional_formatter___closed__4);
l_Lean_Parser_optional_parenthesizer___closed__1 = _init_l_Lean_Parser_optional_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_optional_parenthesizer___closed__1);
l_Lean_Parser_optional___closed__1 = _init_l_Lean_Parser_optional___closed__1();
lean_mark_persistent(l_Lean_Parser_optional___closed__1);
l_Lean_Parser_optional___closed__2 = _init_l_Lean_Parser_optional___closed__2();
lean_mark_persistent(l_Lean_Parser_optional___closed__2);
l_Lean_Parser_optional___closed__3 = _init_l_Lean_Parser_optional___closed__3();
lean_mark_persistent(l_Lean_Parser_optional___closed__3);
l_Lean_Parser_optional___closed__4 = _init_l_Lean_Parser_optional___closed__4();
lean_mark_persistent(l_Lean_Parser_optional___closed__4);
l_Lean_Parser_optional___closed__5 = _init_l_Lean_Parser_optional___closed__5();
lean_mark_persistent(l_Lean_Parser_optional___closed__5);
l_Lean_Parser_many_formatter___closed__1 = _init_l_Lean_Parser_many_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_many_formatter___closed__1);
l_Lean_Parser_many_formatter___closed__2 = _init_l_Lean_Parser_many_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_many_formatter___closed__2);
l_Lean_Parser_many_formatter___closed__3 = _init_l_Lean_Parser_many_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_many_formatter___closed__3);
l_Lean_Parser_many_parenthesizer___closed__1 = _init_l_Lean_Parser_many_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_many_parenthesizer___closed__1);
l_Lean_Parser_many___closed__1 = _init_l_Lean_Parser_many___closed__1();
lean_mark_persistent(l_Lean_Parser_many___closed__1);
l_Lean_Parser_many___closed__2 = _init_l_Lean_Parser_many___closed__2();
lean_mark_persistent(l_Lean_Parser_many___closed__2);
l_Lean_Parser_many___closed__3 = _init_l_Lean_Parser_many___closed__3();
lean_mark_persistent(l_Lean_Parser_many___closed__3);
l_Lean_Parser_many___closed__4 = _init_l_Lean_Parser_many___closed__4();
lean_mark_persistent(l_Lean_Parser_many___closed__4);
l_Lean_Parser_many___closed__5 = _init_l_Lean_Parser_many___closed__5();
lean_mark_persistent(l_Lean_Parser_many___closed__5);
l_Lean_Parser_ident_formatter___closed__1 = _init_l_Lean_Parser_ident_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_ident_formatter___closed__1);
l_Lean_Parser_ident_formatter___closed__2 = _init_l_Lean_Parser_ident_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_ident_formatter___closed__2);
l_Lean_Parser_ident_formatter___closed__3 = _init_l_Lean_Parser_ident_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_ident_formatter___closed__3);
l_Lean_Parser_ident_parenthesizer___closed__1 = _init_l_Lean_Parser_ident_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_ident_parenthesizer___closed__1);
l_Lean_Parser_ident___elambda__1___closed__1 = _init_l_Lean_Parser_ident___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_ident___elambda__1___closed__1);
l_Lean_Parser_ident___elambda__1___closed__2 = _init_l_Lean_Parser_ident___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_ident___elambda__1___closed__2);
l_Lean_Parser_ident___closed__1 = _init_l_Lean_Parser_ident___closed__1();
lean_mark_persistent(l_Lean_Parser_ident___closed__1);
l_Lean_Parser_ident___closed__2 = _init_l_Lean_Parser_ident___closed__2();
lean_mark_persistent(l_Lean_Parser_ident___closed__2);
l_Lean_Parser_ident___closed__3 = _init_l_Lean_Parser_ident___closed__3();
lean_mark_persistent(l_Lean_Parser_ident___closed__3);
l_Lean_Parser_ident___closed__4 = _init_l_Lean_Parser_ident___closed__4();
lean_mark_persistent(l_Lean_Parser_ident___closed__4);
l_Lean_Parser_ident = _init_l_Lean_Parser_ident();
lean_mark_persistent(l_Lean_Parser_ident);
l_Lean_Parser_rawIdent_formatter___closed__1 = _init_l_Lean_Parser_rawIdent_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdent_formatter___closed__1);
l_Lean_Parser_rawIdent_parenthesizer___closed__1 = _init_l_Lean_Parser_rawIdent_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdent_parenthesizer___closed__1);
l_Lean_Parser_rawIdent___elambda__1___closed__1 = _init_l_Lean_Parser_rawIdent___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdent___elambda__1___closed__1);
l_Lean_Parser_rawIdent___closed__1 = _init_l_Lean_Parser_rawIdent___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__1);
l_Lean_Parser_rawIdent___closed__2 = _init_l_Lean_Parser_rawIdent___closed__2();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__2);
l_Lean_Parser_rawIdent___closed__3 = _init_l_Lean_Parser_rawIdent___closed__3();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__3);
l_Lean_Parser_rawIdent___closed__4 = _init_l_Lean_Parser_rawIdent___closed__4();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__4);
l_Lean_Parser_rawIdent___closed__5 = _init_l_Lean_Parser_rawIdent___closed__5();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__5);
l_Lean_Parser_rawIdent = _init_l_Lean_Parser_rawIdent();
lean_mark_persistent(l_Lean_Parser_rawIdent);
l_Lean_Parser_numLit_formatter___closed__1 = _init_l_Lean_Parser_numLit_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit_formatter___closed__1);
l_Lean_Parser_numLit_formatter___closed__2 = _init_l_Lean_Parser_numLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_numLit_formatter___closed__2);
l_Lean_Parser_numLit_formatter___closed__3 = _init_l_Lean_Parser_numLit_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_numLit_formatter___closed__3);
l_Lean_Parser_numLit_formatter___closed__4 = _init_l_Lean_Parser_numLit_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_numLit_formatter___closed__4);
l_Lean_Parser_numLit_parenthesizer___closed__1 = _init_l_Lean_Parser_numLit_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit_parenthesizer___closed__1);
l_Lean_Parser_numLit_parenthesizer___closed__2 = _init_l_Lean_Parser_numLit_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_numLit_parenthesizer___closed__2);
l_Lean_Parser_numLit___elambda__1___closed__1 = _init_l_Lean_Parser_numLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit___elambda__1___closed__1);
l_Lean_Parser_numLit___elambda__1___closed__2 = _init_l_Lean_Parser_numLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_numLit___elambda__1___closed__2);
l_Lean_Parser_numLit___closed__1 = _init_l_Lean_Parser_numLit___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit___closed__1);
l_Lean_Parser_numLit___closed__2 = _init_l_Lean_Parser_numLit___closed__2();
lean_mark_persistent(l_Lean_Parser_numLit___closed__2);
l_Lean_Parser_numLit___closed__3 = _init_l_Lean_Parser_numLit___closed__3();
lean_mark_persistent(l_Lean_Parser_numLit___closed__3);
l_Lean_Parser_numLit___closed__4 = _init_l_Lean_Parser_numLit___closed__4();
lean_mark_persistent(l_Lean_Parser_numLit___closed__4);
l_Lean_Parser_numLit = _init_l_Lean_Parser_numLit();
lean_mark_persistent(l_Lean_Parser_numLit);
l_Lean_Parser_scientificLit_formatter___closed__1 = _init_l_Lean_Parser_scientificLit_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLit_formatter___closed__1);
l_Lean_Parser_scientificLit_formatter___closed__2 = _init_l_Lean_Parser_scientificLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLit_formatter___closed__2);
l_Lean_Parser_scientificLit_formatter___closed__3 = _init_l_Lean_Parser_scientificLit_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_scientificLit_formatter___closed__3);
l_Lean_Parser_scientificLit_formatter___closed__4 = _init_l_Lean_Parser_scientificLit_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_scientificLit_formatter___closed__4);
l_Lean_Parser_scientificLit_parenthesizer___closed__1 = _init_l_Lean_Parser_scientificLit_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLit_parenthesizer___closed__1);
l_Lean_Parser_scientificLit_parenthesizer___closed__2 = _init_l_Lean_Parser_scientificLit_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLit_parenthesizer___closed__2);
l_Lean_Parser_scientificLit___elambda__1___closed__1 = _init_l_Lean_Parser_scientificLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLit___elambda__1___closed__1);
l_Lean_Parser_scientificLit___elambda__1___closed__2 = _init_l_Lean_Parser_scientificLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLit___elambda__1___closed__2);
l_Lean_Parser_scientificLit___closed__1 = _init_l_Lean_Parser_scientificLit___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__1);
l_Lean_Parser_scientificLit___closed__2 = _init_l_Lean_Parser_scientificLit___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__2);
l_Lean_Parser_scientificLit___closed__3 = _init_l_Lean_Parser_scientificLit___closed__3();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__3);
l_Lean_Parser_scientificLit___closed__4 = _init_l_Lean_Parser_scientificLit___closed__4();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__4);
l_Lean_Parser_scientificLit = _init_l_Lean_Parser_scientificLit();
lean_mark_persistent(l_Lean_Parser_scientificLit);
l_Lean_Parser_strLit_formatter___closed__1 = _init_l_Lean_Parser_strLit_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit_formatter___closed__1);
l_Lean_Parser_strLit_formatter___closed__2 = _init_l_Lean_Parser_strLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_strLit_formatter___closed__2);
l_Lean_Parser_strLit_formatter___closed__3 = _init_l_Lean_Parser_strLit_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_strLit_formatter___closed__3);
l_Lean_Parser_strLit_formatter___closed__4 = _init_l_Lean_Parser_strLit_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_strLit_formatter___closed__4);
l_Lean_Parser_strLit_parenthesizer___closed__1 = _init_l_Lean_Parser_strLit_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit_parenthesizer___closed__1);
l_Lean_Parser_strLit_parenthesizer___closed__2 = _init_l_Lean_Parser_strLit_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_strLit_parenthesizer___closed__2);
l_Lean_Parser_strLit___elambda__1___closed__1 = _init_l_Lean_Parser_strLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit___elambda__1___closed__1);
l_Lean_Parser_strLit___elambda__1___closed__2 = _init_l_Lean_Parser_strLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_strLit___elambda__1___closed__2);
l_Lean_Parser_strLit___closed__1 = _init_l_Lean_Parser_strLit___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit___closed__1);
l_Lean_Parser_strLit___closed__2 = _init_l_Lean_Parser_strLit___closed__2();
lean_mark_persistent(l_Lean_Parser_strLit___closed__2);
l_Lean_Parser_strLit___closed__3 = _init_l_Lean_Parser_strLit___closed__3();
lean_mark_persistent(l_Lean_Parser_strLit___closed__3);
l_Lean_Parser_strLit___closed__4 = _init_l_Lean_Parser_strLit___closed__4();
lean_mark_persistent(l_Lean_Parser_strLit___closed__4);
l_Lean_Parser_strLit = _init_l_Lean_Parser_strLit();
lean_mark_persistent(l_Lean_Parser_strLit);
l_Lean_Parser_charLit_formatter___closed__1 = _init_l_Lean_Parser_charLit_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit_formatter___closed__1);
l_Lean_Parser_charLit_formatter___closed__2 = _init_l_Lean_Parser_charLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_charLit_formatter___closed__2);
l_Lean_Parser_charLit_formatter___closed__3 = _init_l_Lean_Parser_charLit_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_charLit_formatter___closed__3);
l_Lean_Parser_charLit_formatter___closed__4 = _init_l_Lean_Parser_charLit_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_charLit_formatter___closed__4);
l_Lean_Parser_charLit_parenthesizer___closed__1 = _init_l_Lean_Parser_charLit_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit_parenthesizer___closed__1);
l_Lean_Parser_charLit_parenthesizer___closed__2 = _init_l_Lean_Parser_charLit_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_charLit_parenthesizer___closed__2);
l_Lean_Parser_charLit___elambda__1___closed__1 = _init_l_Lean_Parser_charLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit___elambda__1___closed__1);
l_Lean_Parser_charLit___elambda__1___closed__2 = _init_l_Lean_Parser_charLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_charLit___elambda__1___closed__2);
l_Lean_Parser_charLit___closed__1 = _init_l_Lean_Parser_charLit___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit___closed__1);
l_Lean_Parser_charLit___closed__2 = _init_l_Lean_Parser_charLit___closed__2();
lean_mark_persistent(l_Lean_Parser_charLit___closed__2);
l_Lean_Parser_charLit___closed__3 = _init_l_Lean_Parser_charLit___closed__3();
lean_mark_persistent(l_Lean_Parser_charLit___closed__3);
l_Lean_Parser_charLit___closed__4 = _init_l_Lean_Parser_charLit___closed__4();
lean_mark_persistent(l_Lean_Parser_charLit___closed__4);
l_Lean_Parser_charLit = _init_l_Lean_Parser_charLit();
lean_mark_persistent(l_Lean_Parser_charLit);
l_Lean_Parser_nameLit_formatter___closed__1 = _init_l_Lean_Parser_nameLit_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLit_formatter___closed__1);
l_Lean_Parser_nameLit_formatter___closed__2 = _init_l_Lean_Parser_nameLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLit_formatter___closed__2);
l_Lean_Parser_nameLit_formatter___closed__3 = _init_l_Lean_Parser_nameLit_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_nameLit_formatter___closed__3);
l_Lean_Parser_nameLit_formatter___closed__4 = _init_l_Lean_Parser_nameLit_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_nameLit_formatter___closed__4);
l_Lean_Parser_nameLit_parenthesizer___closed__1 = _init_l_Lean_Parser_nameLit_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLit_parenthesizer___closed__1);
l_Lean_Parser_nameLit_parenthesizer___closed__2 = _init_l_Lean_Parser_nameLit_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLit_parenthesizer___closed__2);
l_Lean_Parser_nameLit___elambda__1___closed__1 = _init_l_Lean_Parser_nameLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLit___elambda__1___closed__1);
l_Lean_Parser_nameLit___elambda__1___closed__2 = _init_l_Lean_Parser_nameLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLit___elambda__1___closed__2);
l_Lean_Parser_nameLit___closed__1 = _init_l_Lean_Parser_nameLit___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__1);
l_Lean_Parser_nameLit___closed__2 = _init_l_Lean_Parser_nameLit___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__2);
l_Lean_Parser_nameLit___closed__3 = _init_l_Lean_Parser_nameLit___closed__3();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__3);
l_Lean_Parser_nameLit___closed__4 = _init_l_Lean_Parser_nameLit___closed__4();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__4);
l_Lean_Parser_nameLit = _init_l_Lean_Parser_nameLit();
lean_mark_persistent(l_Lean_Parser_nameLit);
l_Lean_Parser_many1Indent_formatter___closed__1 = _init_l_Lean_Parser_many1Indent_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Indent_formatter___closed__1);
l_Lean_Parser_many1Indent_parenthesizer___closed__1 = _init_l_Lean_Parser_many1Indent_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Indent_parenthesizer___closed__1);
l_Lean_Parser_many1Indent___closed__1 = _init_l_Lean_Parser_many1Indent___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Indent___closed__1);
l_Lean_Parser_many1Indent___closed__2 = _init_l_Lean_Parser_many1Indent___closed__2();
lean_mark_persistent(l_Lean_Parser_many1Indent___closed__2);
l_Lean_Parser_ppHardSpace___closed__1 = _init_l_Lean_Parser_ppHardSpace___closed__1();
lean_mark_persistent(l_Lean_Parser_ppHardSpace___closed__1);
l_Lean_Parser_ppHardSpace___closed__2 = _init_l_Lean_Parser_ppHardSpace___closed__2();
lean_mark_persistent(l_Lean_Parser_ppHardSpace___closed__2);
l_Lean_Parser_ppHardSpace = _init_l_Lean_Parser_ppHardSpace();
lean_mark_persistent(l_Lean_Parser_ppHardSpace);
l_Lean_Parser_ppSpace = _init_l_Lean_Parser_ppSpace();
lean_mark_persistent(l_Lean_Parser_ppSpace);
l_Lean_Parser_ppLine = _init_l_Lean_Parser_ppLine();
lean_mark_persistent(l_Lean_Parser_ppLine);
l_Lean_ppHardSpace_formatter___closed__1 = _init_l_Lean_ppHardSpace_formatter___closed__1();
lean_mark_persistent(l_Lean_ppHardSpace_formatter___closed__1);
l_Lean_ppHardSpace_formatter___closed__2 = _init_l_Lean_ppHardSpace_formatter___closed__2();
lean_mark_persistent(l_Lean_ppHardSpace_formatter___closed__2);
l_Lean_ppLine_formatter___closed__1 = _init_l_Lean_ppLine_formatter___closed__1();
lean_mark_persistent(l_Lean_ppLine_formatter___closed__1);
l_Lean_ppLine_formatter___closed__2 = _init_l_Lean_ppLine_formatter___closed__2();
lean_mark_persistent(l_Lean_ppLine_formatter___closed__2);
l_Lean_ppDedent_formatter___closed__1 = _init_l_Lean_ppDedent_formatter___closed__1();
lean_mark_persistent(l_Lean_ppDedent_formatter___closed__1);
l_Lean_Parser_termRegister__parser__alias_________closed__1 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__1();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__1);
l_Lean_Parser_termRegister__parser__alias_________closed__2 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__2();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__2);
l_Lean_Parser_termRegister__parser__alias_________closed__3 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__3();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__3);
l_Lean_Parser_termRegister__parser__alias_________closed__4 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__4();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__4);
l_Lean_Parser_termRegister__parser__alias_________closed__5 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__5();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__5);
l_Lean_Parser_termRegister__parser__alias_________closed__6 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__6();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__6);
l_Lean_Parser_termRegister__parser__alias_________closed__7 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__7();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__7);
l_Lean_Parser_termRegister__parser__alias_________closed__8 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__8();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__8);
l_Lean_Parser_termRegister__parser__alias_________closed__9 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__9();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__9);
l_Lean_Parser_termRegister__parser__alias_________closed__10 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__10();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__10);
l_Lean_Parser_termRegister__parser__alias_________closed__11 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__11();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__11);
l_Lean_Parser_termRegister__parser__alias_________closed__12 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__12();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__12);
l_Lean_Parser_termRegister__parser__alias_________closed__13 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__13();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__13);
l_Lean_Parser_termRegister__parser__alias_________closed__14 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__14();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__14);
l_Lean_Parser_termRegister__parser__alias_________closed__15 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__15();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__15);
l_Lean_Parser_termRegister__parser__alias_________closed__16 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__16();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__16);
l_Lean_Parser_termRegister__parser__alias_________closed__17 = _init_l_Lean_Parser_termRegister__parser__alias_________closed__17();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_________closed__17);
l_Lean_Parser_termRegister__parser__alias______ = _init_l_Lean_Parser_termRegister__parser__alias______();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias______);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__1);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__2);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__3);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__4);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__5);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__6);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__7);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__8);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__9);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__10);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__11);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__12);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__13);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__14);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__15);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__16);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__17);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__18);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__19);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__20);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__21);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__22);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__23);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__24);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__25);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__26);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__27);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__28);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__29);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__30);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__31);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__32);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__33);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__34);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__35);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__36);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__37);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__38);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__39);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__40);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__41);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__42);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__43);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__44);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__45);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__46);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__47);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__48);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__49);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__50);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__51);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__52);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__53);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__54);
l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55 = _init_l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55();
lean_mark_persistent(l_Lean_Parser_myMacro____x40_Lean_Parser_Extra___hyg_256____closed__55);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__7);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__8);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__9);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__10);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__11);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__12);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__13);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__14);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__15);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__16);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__17);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__18);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__19);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__20);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__21);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__22);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__23);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__24);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__25);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__26);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__27);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__28);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__29);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__30);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__31);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__32);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__33);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__34);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__35);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__36);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__37);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__38);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__39);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__40);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__41);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__42);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__43);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__44);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__45);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__46);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__47);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__48);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__49);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__50);
l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486____closed__51);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_486_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
