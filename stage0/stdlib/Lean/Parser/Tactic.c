// Lean compiler output
// Module: Lean.Parser.Tactic
// Imports: Init Lean.Parser.Term
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
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__7;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2;
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_formatter(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_match___closed__7;
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_formatter(lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_match;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__2;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTactic;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1;
lean_object* l_Lean_Parser_Term_matchAlts(lean_object*);
extern lean_object* l_Lean_Parser_leadPrec;
lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_match___closed__10;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__7;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__11;
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2;
extern lean_object* l_Lean_Parser_errorAtSavedPos___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs;
extern lean_object* l_Lean_Parser_Term_simpleBinder_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__6;
lean_object* l_Lean_Parser_Tactic_introMatch_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_introMatch(lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__4;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed;
lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8;
lean_object* l_Lean_Parser_tokenWithAntiquotFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1;
extern lean_object* l_Lean_Parser_ident;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__6;
lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchAlts___closed__1;
lean_object* l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_unknown(lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs___closed__1;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__3;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__5;
lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_decide___closed__6;
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_syntheticHole___closed__7;
lean_object* l_Lean_Parser_Tactic_decide_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Tactic_nativeDecide;
extern lean_object* l_Lean_Parser_Term_hole___closed__5;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__12;
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__5;
lean_object* l_Lean_Parser_Tactic_unknown___closed__1;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs___closed__4;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs___closed__2;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2;
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer(lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_574____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_decide___closed__1;
lean_object* l_Lean_Parser_Tactic_decide_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__1;
lean_object* l_Lean_Parser_Term_matchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__7;
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Tactic_decide___closed__2;
extern lean_object* l___regBuiltin_Lean_Parser_Term_hole_parenthesizer___closed__1;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nativeDecide(lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__3;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_mkAntiquot___closed__18;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__4;
extern lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__8;
extern lean_object* l_Lean_Parser_Term_structInst_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__5;
lean_object* l_Lean_Parser_Tactic_decide___closed__4;
extern lean_object* l_Lean_Parser_Term_optType;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___closed__6;
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__2;
lean_object* l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__8;
extern lean_object* l_Lean_Parser_Term_byTactic_formatter___closed__3;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__7;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__1;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_eraseAuxDiscrs(lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__2;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1;
extern lean_object* l_Lean_Parser_Term_byTactic_parenthesizer___closed__2;
lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_decide___closed__5;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6;
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__19;
extern lean_object* l_Lean_Parser_parserAliasesRef;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_match___closed__6;
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__5;
lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__3;
extern lean_object* l___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_decide___closed__3;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__5;
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_Tactic_match___closed__8;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__1;
extern lean_object* l_Lean_Parser_Term_simpleBinder_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_introMatch___closed__8;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__3;
lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3;
lean_object* l_Lean_Parser_Tactic_match___closed__9;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_Term_match_formatter___closed__4;
lean_object* l_Lean_Parser_Tactic_nativeDecide_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___closed__4;
lean_object* l_Lean_Parser_Tactic_matchRhs___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter(lean_object*);
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__7;
lean_object* l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4;
extern lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__5;
lean_object* l_Lean_Parser_Tactic_match___closed__2;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5;
lean_object* l_Lean_Parser_Tactic_unknown_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___closed__7;
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic(lean_object*);
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__5;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_match(lean_object*);
lean_object* l_Lean_Parser_Tactic_match___closed__4;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_match___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_matchRhs_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_match___closed__3;
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Tactic_decide_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3;
extern lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
lean_object* l_Lean_Parser_Tactic_decide_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_match___closed__5;
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__6;
lean_object* l_Lean_Parser_Tactic_decide_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_matchRhs___closed__3;
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_match_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
lean_object* l_Lean_Parser_Tactic_decide;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__10;
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Term_syntheticHole_formatter___closed__1;
extern lean_object* l_Lean_Parser_Tactic_tacticSeq;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Tactic_case___closed__8;
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6;
extern lean_object* l_Lean_Parser_Term_match___closed__4;
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__8;
extern lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__2;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_decide(lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__4;
extern lean_object* l_Lean_Parser_Term_match_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Tactic_decide_formatter___closed__3;
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_formatter(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_hole;
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter(lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Term_hole_formatter___closed__1;
lean_object* l_String_trim(lean_object*);
extern lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__3;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_unknown___closed__6;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__6;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5_(lean_object*);
lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__4;
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5;
lean_object* l_Lean_Parser_Tactic_decide___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_matchRhs;
extern lean_object* l_Lean_Parser_Tactic_intro___closed__2;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3;
lean_object* l_Lean_Parser_Tactic_nativeDecide_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide___closed__7;
lean_object* l_Lean_Parser_Tactic_unknown___closed__3;
lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2;
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1;
extern lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_unknown___closed__5;
extern lean_object* l_Lean_Parser_Tactic_intro___closed__5;
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_matchAlts;
lean_object* l_Lean_Parser_Tactic_match_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object*);
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_decide_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_decide___closed__7;
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_match_formatter___closed__5;
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7;
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__10;
lean_object* l_Lean_Parser_Tactic_introMatch;
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter(lean_object*);
lean_object* l_Lean_Parser_Tactic_matchAlts_formatter___closed__1;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_match___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1;
lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9;
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_syntheticHole;
static lean_object* _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_tacticSeq;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_byTactic_formatter___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_byTactic_parenthesizer___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_parserAliasesRef;
x_3 = l_Lean_Parser_Tactic_case___closed__8;
x_4 = l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_8 = l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_7, x_3, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_12 = l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_11, x_3, x_12, x_10);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown tactic");
return x_1;
}
}
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_1, 4, x_10);
lean_inc(x_1);
x_11 = l_Lean_Parser_ident___elambda__1(x_1, x_2);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_574____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_16 = 1;
x_17 = l_Lean_Parser_errorAtSavedPosFn(x_15, x_16, x_1, x_11);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_1, 4, x_24);
lean_ctor_set(x_1, 1, x_22);
lean_inc(x_1);
x_25 = l_Lean_Parser_ident___elambda__1(x_1, x_2);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
x_27 = lean_box(0);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_574____at_Lean_Parser_ParserState_hasError___spec__1(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_30 = 1;
x_31 = l_Lean_Parser_errorAtSavedPosFn(x_29, x_30, x_1, x_25);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_ctor_get(x_4, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_5, 3);
lean_inc(x_39);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_40 = x_5;
} else {
 lean_dec_ref(x_5);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 4, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_1, 4, x_43);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_35);
lean_inc(x_1);
x_44 = l_Lean_Parser_ident___elambda__1(x_1, x_2);
x_45 = lean_ctor_get(x_44, 4);
lean_inc(x_45);
x_46 = lean_box(0);
x_47 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_574____at_Lean_Parser_ParserState_hasError___spec__1(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_dec(x_1);
return x_44;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_49 = 1;
x_50 = l_Lean_Parser_errorAtSavedPosFn(x_48, x_49, x_1, x_44);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_56 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_57 = lean_ctor_get(x_1, 5);
lean_inc(x_57);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 2);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_52, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 3);
lean_inc(x_66);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_67 = x_52;
} else {
 lean_dec_ref(x_52);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 4, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_66);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set(x_71, 3, x_54);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_57);
lean_ctor_set_uint8(x_71, sizeof(void*)*6, x_55);
lean_ctor_set_uint8(x_71, sizeof(void*)*6 + 1, x_56);
lean_inc(x_71);
x_72 = l_Lean_Parser_ident___elambda__1(x_71, x_2);
x_73 = lean_ctor_get(x_72, 4);
lean_inc(x_73);
x_74 = lean_box(0);
x_75 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_574____at_Lean_Parser_ParserState_hasError___spec__1(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_dec(x_71);
return x_72;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_76 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_77 = 1;
x_78 = l_Lean_Parser_errorAtSavedPosFn(x_76, x_77, x_71, x_72);
return x_78;
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_FirstTokens_toStr___closed__2;
x_2 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__2;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__5;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___closed__10;
x_2 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_unknown___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__7;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_unknown___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_unknown___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_unknown___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_unknown___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_unknown___closed__5;
x_2 = l_Lean_Parser_Tactic_unknown___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_unknown___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_unknown(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_unknown;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_FirstTokens_toStr___closed__2;
x_2 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__2;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_formatter___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed), 6, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1057____closed__11;
x_2 = l_Lean_Parser_Tactic_unknown_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_unknown_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withPosition_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_unknown_formatter___closed__4;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_unknown_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_unknown_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_unknown_formatter___closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__2;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed), 6, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__19;
x_2 = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_unknown___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nestedTactic() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_tacticSeqBracketed;
return x_1;
}
}
static lean_object* _init_l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nestedTactic");
return x_1;
}
}
static lean_object* _init_l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_nestedTactic;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTactic_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTactic_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eraseAuxDiscrs");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eraseAuxDiscrs!");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9;
x_2 = l_Lean_Parser_mkAntiquot___closed__18;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_fun___elambda__1___closed__10;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_eraseAuxDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_eraseAuxDiscrs;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__1;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_tacticSeq;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_syntheticHole___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_matchRhs___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_Term_hole___closed__5;
x_4 = l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1;
x_5 = 1;
x_6 = l_Lean_Parser_orelseFnCore(x_3, x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_syntheticHole;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_tacticSeq;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_hole;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_matchRhs___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_matchRhs___closed__2;
x_2 = l_Lean_Parser_Tactic_matchRhs___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_matchRhs___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_matchRhs;
x_2 = l_Lean_Parser_Term_matchAlts(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_matchAlts___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
x_2 = l_Lean_Parser_Tactic_match___elambda__1___closed__2;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_matchAlts;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_structInst___elambda__1___closed__6;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_optType;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__4;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_match___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_match___elambda__1___closed__11;
x_2 = l_Lean_Parser_Tactic_match___elambda__1___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_match___elambda__1___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__8;
x_2 = l_Lean_Parser_Term_byTactic___elambda__1___closed__10;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__8;
x_2 = l_Lean_Parser_Tactic_match___elambda__1___closed__9;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_match___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_match___elambda__1___closed__10;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_matchAlts;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_structInst___elambda__1___closed__4;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_optType;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_match___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_match___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_match___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_match___closed__4;
x_2 = l_Lean_Parser_Tactic_match___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_match___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_match___closed__5;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_match___closed__6;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_match___closed__7;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_match___closed__8;
x_2 = l_Lean_Parser_Tactic_match___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_match___closed__10;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_match(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_match;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Term_syntheticHole_formatter___closed__1;
x_2 = l_Lean_Parser_Term_byTactic_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_matchRhs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l___regBuiltin_Lean_Parser_Term_hole_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_matchRhs_formatter___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Tactic_matchAlts_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_Tactic_matchAlts_formatter___closed__1;
x_7 = l_Lean_Parser_Term_matchAlts_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
x_2 = l_Lean_Parser_Tactic_match___elambda__1___closed__2;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_structInst_formatter___closed__2;
x_2 = l_Lean_Parser_Tactic_match_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_simpleBinder_formatter___closed__2;
x_2 = l_Lean_Parser_Tactic_match_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_match_formatter___closed__4;
x_2 = l_Lean_Parser_Tactic_match_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_match_formatter___closed__2;
x_2 = l_Lean_Parser_Tactic_match_formatter___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_2 = l_Lean_Parser_leadPrec;
x_3 = l_Lean_Parser_Tactic_match_formatter___closed__6;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_match_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_match_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_match_formatter___closed__7;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1;
x_2 = l_Lean_Parser_Term_byTactic_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l___regBuiltin_Lean_Parser_Term_hole_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_matchAlts_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__2;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_parenthesizer), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__1;
x_2 = l_Lean_Parser_Tactic_match_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_simpleBinder_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Tactic_match_parenthesizer___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_match_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Tactic_match_parenthesizer___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__1;
x_2 = l_Lean_Parser_Tactic_match_parenthesizer___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_2 = l_Lean_Parser_leadPrec;
x_3 = l_Lean_Parser_Tactic_match_parenthesizer___closed__6;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_match_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_match_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_match_parenthesizer___closed__7;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introMatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_intro___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_matchAlts;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___closed__10;
x_2 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_introMatch___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_matchAlts;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_introMatch___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_introMatch___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___closed__3;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_introMatch___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_introMatch___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch___closed__6;
x_2 = l_Lean_Parser_Tactic_introMatch___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_introMatch___closed__8;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_introMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_introMatch;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_intro___closed__5;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_introMatch_formatter___closed__2;
x_2 = l_Lean_Parser_Tactic_match_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_introMatch_formatter___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_introMatch_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_introMatch_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_introMatch_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__5;
x_2 = l_Lean_Parser_Tactic_match_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
x_2 = l_Lean_Parser_Tactic_decide___elambda__1___closed__2;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_decide___elambda__1___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__7;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___closed__10;
x_2 = l_Lean_Parser_Tactic_decide___elambda__1___closed__8;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_decide___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_decide___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_decide___elambda__1___closed__9;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__4;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_decide___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_decide___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_decide___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_decide___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_decide___closed__5;
x_2 = l_Lean_Parser_Tactic_decide___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_decide___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_decide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_decide;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
x_2 = l_Lean_Parser_Tactic_decide___elambda__1___closed__2;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide_formatter___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6195____closed__24;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_decide_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_decide_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_decide_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_decide_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_decide_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__2;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_decide_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_decide_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_decide_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_decide_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_decide_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_decide___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nativeDecide");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__2;
x_2 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___closed__10;
x_2 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_nativeDecide___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10;
x_6 = 1;
x_7 = l_Lean_Parser_orelseFnCore(x_4, x_5, x_6, x_1, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nativeDecide___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_nativeDecide___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_nativeDecide___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nativeDecide___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___closed__5;
x_2 = l_Lean_Parser_Tactic_nativeDecide___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nativeDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_3 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_nativeDecide;
x_6 = lean_unsigned_to_nat(1000u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_nativeDecide_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1;
x_7 = l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nativeDecide_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_nativeDecide_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nativeDecide_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Tactic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1 = _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__1);
l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2 = _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__2);
l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3 = _init_l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5____closed__3);
res = l_Lean_Parser_Tactic_initFn____x40_Lean_Parser_Tactic___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___lambda__1___closed__1);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__1);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__2);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__3);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__4);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__5);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__6);
l_Lean_Parser_Tactic_unknown___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_unknown___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___elambda__1___closed__7);
l_Lean_Parser_Tactic_unknown___closed__1 = _init_l_Lean_Parser_Tactic_unknown___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__1);
l_Lean_Parser_Tactic_unknown___closed__2 = _init_l_Lean_Parser_Tactic_unknown___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__2);
l_Lean_Parser_Tactic_unknown___closed__3 = _init_l_Lean_Parser_Tactic_unknown___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__3);
l_Lean_Parser_Tactic_unknown___closed__4 = _init_l_Lean_Parser_Tactic_unknown___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__4);
l_Lean_Parser_Tactic_unknown___closed__5 = _init_l_Lean_Parser_Tactic_unknown___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__5);
l_Lean_Parser_Tactic_unknown___closed__6 = _init_l_Lean_Parser_Tactic_unknown___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__6);
l_Lean_Parser_Tactic_unknown___closed__7 = _init_l_Lean_Parser_Tactic_unknown___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown___closed__7);
l_Lean_Parser_Tactic_unknown = _init_l_Lean_Parser_Tactic_unknown();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown);
res = l___regBuiltinParser_Lean_Parser_Tactic_unknown(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_unknown_formatter___closed__1 = _init_l_Lean_Parser_Tactic_unknown_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_formatter___closed__1);
l_Lean_Parser_Tactic_unknown_formatter___closed__2 = _init_l_Lean_Parser_Tactic_unknown_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_formatter___closed__2);
l_Lean_Parser_Tactic_unknown_formatter___closed__3 = _init_l_Lean_Parser_Tactic_unknown_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_formatter___closed__3);
l_Lean_Parser_Tactic_unknown_formatter___closed__4 = _init_l_Lean_Parser_Tactic_unknown_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_formatter___closed__4);
l_Lean_Parser_Tactic_unknown_formatter___closed__5 = _init_l_Lean_Parser_Tactic_unknown_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_formatter___closed__5);
l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_unknown_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_unknown_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1);
l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2);
l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3 = _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3);
l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4 = _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4);
l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5 = _init_l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5);
l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nestedTactic = _init_l_Lean_Parser_Tactic_nestedTactic();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTactic);
l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__1);
l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2 = _init_l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic___closed__2);
res = l___regBuiltinParser_Lean_Parser_Tactic_nestedTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_nestedTactic_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__1);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__3);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__4);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__6);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__7);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__8);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__9);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__10);
l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__11);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__1);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__2);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__3);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__4);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__5);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__6);
l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs___closed__7);
l_Lean_Parser_Tactic_eraseAuxDiscrs = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs);
res = l___regBuiltinParser_Lean_Parser_Tactic_eraseAuxDiscrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1);
l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__2);
l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__3);
l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1);
l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__2);
l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_eraseAuxDiscrs_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs___elambda__1___closed__1);
l_Lean_Parser_Tactic_matchRhs___closed__1 = _init_l_Lean_Parser_Tactic_matchRhs___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs___closed__1);
l_Lean_Parser_Tactic_matchRhs___closed__2 = _init_l_Lean_Parser_Tactic_matchRhs___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs___closed__2);
l_Lean_Parser_Tactic_matchRhs___closed__3 = _init_l_Lean_Parser_Tactic_matchRhs___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs___closed__3);
l_Lean_Parser_Tactic_matchRhs___closed__4 = _init_l_Lean_Parser_Tactic_matchRhs___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs___closed__4);
l_Lean_Parser_Tactic_matchRhs = _init_l_Lean_Parser_Tactic_matchRhs();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs);
l_Lean_Parser_Tactic_matchAlts___closed__1 = _init_l_Lean_Parser_Tactic_matchAlts___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts___closed__1);
l_Lean_Parser_Tactic_matchAlts = _init_l_Lean_Parser_Tactic_matchAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts);
l_Lean_Parser_Tactic_match___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__1);
l_Lean_Parser_Tactic_match___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__2);
l_Lean_Parser_Tactic_match___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__3);
l_Lean_Parser_Tactic_match___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__4);
l_Lean_Parser_Tactic_match___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__5);
l_Lean_Parser_Tactic_match___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__6);
l_Lean_Parser_Tactic_match___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__7);
l_Lean_Parser_Tactic_match___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__8);
l_Lean_Parser_Tactic_match___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__9);
l_Lean_Parser_Tactic_match___elambda__1___closed__10 = _init_l_Lean_Parser_Tactic_match___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_match___elambda__1___closed__10);
l_Lean_Parser_Tactic_match___closed__1 = _init_l_Lean_Parser_Tactic_match___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__1);
l_Lean_Parser_Tactic_match___closed__2 = _init_l_Lean_Parser_Tactic_match___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__2);
l_Lean_Parser_Tactic_match___closed__3 = _init_l_Lean_Parser_Tactic_match___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__3);
l_Lean_Parser_Tactic_match___closed__4 = _init_l_Lean_Parser_Tactic_match___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__4);
l_Lean_Parser_Tactic_match___closed__5 = _init_l_Lean_Parser_Tactic_match___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__5);
l_Lean_Parser_Tactic_match___closed__6 = _init_l_Lean_Parser_Tactic_match___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__6);
l_Lean_Parser_Tactic_match___closed__7 = _init_l_Lean_Parser_Tactic_match___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__7);
l_Lean_Parser_Tactic_match___closed__8 = _init_l_Lean_Parser_Tactic_match___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__8);
l_Lean_Parser_Tactic_match___closed__9 = _init_l_Lean_Parser_Tactic_match___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__9);
l_Lean_Parser_Tactic_match___closed__10 = _init_l_Lean_Parser_Tactic_match___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_match___closed__10);
l_Lean_Parser_Tactic_match = _init_l_Lean_Parser_Tactic_match();
lean_mark_persistent(l_Lean_Parser_Tactic_match);
res = l___regBuiltinParser_Lean_Parser_Tactic_match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_matchRhs_formatter___closed__1 = _init_l_Lean_Parser_Tactic_matchRhs_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs_formatter___closed__1);
l_Lean_Parser_Tactic_matchAlts_formatter___closed__1 = _init_l_Lean_Parser_Tactic_matchAlts_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts_formatter___closed__1);
l_Lean_Parser_Tactic_match_formatter___closed__1 = _init_l_Lean_Parser_Tactic_match_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__1);
l_Lean_Parser_Tactic_match_formatter___closed__2 = _init_l_Lean_Parser_Tactic_match_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__2);
l_Lean_Parser_Tactic_match_formatter___closed__3 = _init_l_Lean_Parser_Tactic_match_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__3);
l_Lean_Parser_Tactic_match_formatter___closed__4 = _init_l_Lean_Parser_Tactic_match_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__4);
l_Lean_Parser_Tactic_match_formatter___closed__5 = _init_l_Lean_Parser_Tactic_match_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__5);
l_Lean_Parser_Tactic_match_formatter___closed__6 = _init_l_Lean_Parser_Tactic_match_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__6);
l_Lean_Parser_Tactic_match_formatter___closed__7 = _init_l_Lean_Parser_Tactic_match_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_match_formatter___closed__7);
l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_match_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_match_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1);
l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts_parenthesizer___closed__1);
l_Lean_Parser_Tactic_match_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__1);
l_Lean_Parser_Tactic_match_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__2);
l_Lean_Parser_Tactic_match_parenthesizer___closed__3 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__3);
l_Lean_Parser_Tactic_match_parenthesizer___closed__4 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__4);
l_Lean_Parser_Tactic_match_parenthesizer___closed__5 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__5);
l_Lean_Parser_Tactic_match_parenthesizer___closed__6 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__6);
l_Lean_Parser_Tactic_match_parenthesizer___closed__7 = _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_match_parenthesizer___closed__7);
l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_match_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__1);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__2);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__3);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__4);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__5);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__6);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__7);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__8);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__9);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__10);
l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11 = _init_l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___elambda__1___closed__11);
l_Lean_Parser_Tactic_introMatch___closed__1 = _init_l_Lean_Parser_Tactic_introMatch___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__1);
l_Lean_Parser_Tactic_introMatch___closed__2 = _init_l_Lean_Parser_Tactic_introMatch___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__2);
l_Lean_Parser_Tactic_introMatch___closed__3 = _init_l_Lean_Parser_Tactic_introMatch___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__3);
l_Lean_Parser_Tactic_introMatch___closed__4 = _init_l_Lean_Parser_Tactic_introMatch___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__4);
l_Lean_Parser_Tactic_introMatch___closed__5 = _init_l_Lean_Parser_Tactic_introMatch___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__5);
l_Lean_Parser_Tactic_introMatch___closed__6 = _init_l_Lean_Parser_Tactic_introMatch___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__6);
l_Lean_Parser_Tactic_introMatch___closed__7 = _init_l_Lean_Parser_Tactic_introMatch___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__7);
l_Lean_Parser_Tactic_introMatch___closed__8 = _init_l_Lean_Parser_Tactic_introMatch___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch___closed__8);
l_Lean_Parser_Tactic_introMatch = _init_l_Lean_Parser_Tactic_introMatch();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch);
res = l___regBuiltinParser_Lean_Parser_Tactic_introMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_introMatch_formatter___closed__1 = _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_formatter___closed__1);
l_Lean_Parser_Tactic_introMatch_formatter___closed__2 = _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_formatter___closed__2);
l_Lean_Parser_Tactic_introMatch_formatter___closed__3 = _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_formatter___closed__3);
l_Lean_Parser_Tactic_introMatch_formatter___closed__4 = _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_formatter___closed__4);
l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_introMatch_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1);
l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2);
l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3 = _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3);
l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_decide___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__1);
l_Lean_Parser_Tactic_decide___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__2);
l_Lean_Parser_Tactic_decide___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__3);
l_Lean_Parser_Tactic_decide___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__4);
l_Lean_Parser_Tactic_decide___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__5);
l_Lean_Parser_Tactic_decide___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__6);
l_Lean_Parser_Tactic_decide___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__7);
l_Lean_Parser_Tactic_decide___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__8);
l_Lean_Parser_Tactic_decide___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_decide___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___elambda__1___closed__9);
l_Lean_Parser_Tactic_decide___closed__1 = _init_l_Lean_Parser_Tactic_decide___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__1);
l_Lean_Parser_Tactic_decide___closed__2 = _init_l_Lean_Parser_Tactic_decide___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__2);
l_Lean_Parser_Tactic_decide___closed__3 = _init_l_Lean_Parser_Tactic_decide___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__3);
l_Lean_Parser_Tactic_decide___closed__4 = _init_l_Lean_Parser_Tactic_decide___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__4);
l_Lean_Parser_Tactic_decide___closed__5 = _init_l_Lean_Parser_Tactic_decide___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__5);
l_Lean_Parser_Tactic_decide___closed__6 = _init_l_Lean_Parser_Tactic_decide___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__6);
l_Lean_Parser_Tactic_decide___closed__7 = _init_l_Lean_Parser_Tactic_decide___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_decide___closed__7);
l_Lean_Parser_Tactic_decide = _init_l_Lean_Parser_Tactic_decide();
lean_mark_persistent(l_Lean_Parser_Tactic_decide);
res = l___regBuiltinParser_Lean_Parser_Tactic_decide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_decide_formatter___closed__1 = _init_l_Lean_Parser_Tactic_decide_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_decide_formatter___closed__1);
l_Lean_Parser_Tactic_decide_formatter___closed__2 = _init_l_Lean_Parser_Tactic_decide_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_decide_formatter___closed__2);
l_Lean_Parser_Tactic_decide_formatter___closed__3 = _init_l_Lean_Parser_Tactic_decide_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_decide_formatter___closed__3);
l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_decide_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_decide_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_decide_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_decide_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_decide_parenthesizer___closed__1);
l_Lean_Parser_Tactic_decide_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_decide_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_decide_parenthesizer___closed__2);
l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_decide_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__1);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__2);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__3);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__4);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__5);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__6);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__7);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__8);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__9);
l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10 = _init_l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___elambda__1___closed__10);
l_Lean_Parser_Tactic_nativeDecide___closed__1 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__1);
l_Lean_Parser_Tactic_nativeDecide___closed__2 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__2);
l_Lean_Parser_Tactic_nativeDecide___closed__3 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__3);
l_Lean_Parser_Tactic_nativeDecide___closed__4 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__4);
l_Lean_Parser_Tactic_nativeDecide___closed__5 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__5);
l_Lean_Parser_Tactic_nativeDecide___closed__6 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__6);
l_Lean_Parser_Tactic_nativeDecide___closed__7 = _init_l_Lean_Parser_Tactic_nativeDecide___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide___closed__7);
l_Lean_Parser_Tactic_nativeDecide = _init_l_Lean_Parser_Tactic_nativeDecide();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide);
res = l___regBuiltinParser_Lean_Parser_Tactic_nativeDecide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1 = _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide_formatter___closed__1);
l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2 = _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide_formatter___closed__2);
l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3 = _init_l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide_formatter___closed__3);
l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_nativeDecide_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1 = _init_l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1);
l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2 = _init_l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__2);
l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Tactic_nativeDecide_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
