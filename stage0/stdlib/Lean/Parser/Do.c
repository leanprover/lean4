// Lean compiler output
// Module: Lean.Parser.Do
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
lean_object* l_Lean_Parser_Term_do___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr___closed__1;
lean_object* l_Lean_Parser_Term_doPat___closed__7;
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2;
extern lean_object* l_Lean_Parser_Term_have_formatter___closed__2;
lean_object* l_Lean_Parser_Term_doPat_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_doElemParser(lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__1;
lean_object* l_Lean_Parser_Term_doLet___closed__6;
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__2;
lean_object* l_Lean_Parser_Term_doId___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__2;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Term_do_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doPat___closed__3;
lean_object* l_Lean_Parser_Term_leftArrow_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer___closed__4;
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_notFollowedByFn___closed__1;
lean_object* l_Lean_Parser_Term_doAssign_formatter___closed__1;
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_do_formatter___closed__3;
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
lean_object* l___regBuiltinParser_Lean_Parser_Term_doHave(lean_object*);
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer___closed__4;
lean_object* l_Lean_Parser_Term_doExpr___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__4;
lean_object* l_Lean_Parser_Term_doHave_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr___closed__4;
lean_object* l_Lean_Parser_Term_do_parenthesizer___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_liftMethod(lean_object*);
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_structInst_parenthesizer___closed__7;
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeq___elambda__1(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Term_ident_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_do___closed__3;
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__9;
lean_object* l_Lean_Parser_Term_doAssign_formatter___closed__4;
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__8;
lean_object* l_Lean_Parser_Term_doId___closed__5;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__2;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doPat;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doId_formatter___closed__2;
lean_object* l_Lean_Parser_Term_do_formatter___closed__4;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___closed__2;
extern lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doLet_formatter___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_do(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_indentedNonEmptySeq___closed__3;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
lean_object* l_Lean_Parser_doElemParser_formatter(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doPat___closed__4;
lean_object* l_Lean_Parser_Term_doId___closed__2;
extern lean_object* l_Lean_Parser_Term_let_formatter___closed__2;
lean_object* l_Lean_Parser_Term_doExpr___closed__6;
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doAssign___closed__4;
lean_object* l_Lean_Parser_regDoElemParserAttribute___closed__1;
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__5;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Term_doId___closed__1;
extern lean_object* l_Lean_Parser_Term_subtype_formatter___closed__6;
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___closed__8;
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__6;
lean_object* l_Lean_Parser_Term_doAssign_formatter___closed__2;
lean_object* l_Lean_Parser_regDoElemParserAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_try_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_do_formatter___closed__5;
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__5;
extern lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doId___closed__8;
lean_object* l_Lean_Parser_Term_doPat___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doId___closed__4;
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doSeq_formatter___closed__2;
lean_object* l_Lean_Parser_Term_liftMethod___closed__5;
lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_doPat___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doSeqIndent___closed__1;
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doLet_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_formatter(lean_object*);
extern lean_object* l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__6;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_Term_liftMethod_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeq_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doId_formatter___closed__4;
lean_object* l_Lean_Parser_Term_do___closed__1;
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___closed__1;
lean_object* l_Lean_Parser_Term_do___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1;
extern lean_object* l_Lean_Parser_Term_optType;
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3;
extern lean_object* l_Lean_Parser_Tactic_indentedNonEmptySeq_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeq___closed__1;
lean_object* l_Lean_Parser_Term_doSeqIndent___closed__2;
lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_letDecl;
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_doHave_formatter___closed__2;
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doAssign___elambda__1(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___closed__11;
lean_object* l_Lean_Parser_Term_doHave_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_leftArrow___closed__3;
lean_object* l_Lean_Parser_Term_doExpr_formatter___closed__3;
lean_object* l_Lean_Parser_Term_doHave_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doLet___closed__3;
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_Term_doSeq;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_Term_let_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do___closed__6;
lean_object* l_Lean_Parser_Term_doHave_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_doSeqIndent___closed__4;
extern lean_object* l_Lean_Parser_Term_have_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doLet_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__6;
lean_object* l_Lean_Parser_doElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doHave_parenthesizer___closed__3;
extern lean_object* l_Char_HasRepr___closed__1;
extern lean_object* l_Lean_Parser_Term_emptyC___closed__2;
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doAssign_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doLet_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doSeq___closed__2;
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_formatter(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer(lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__7;
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__6;
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doId_parenthesizer___closed__2;
extern lean_object* l_Lean_Parser_Term_subtype_parenthesizer___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_do;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_formatter(lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_liftMethod___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr(lean_object*);
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doSeq_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doId_formatter___closed__5;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__2;
lean_object* l_Lean_Parser_Term_doSeqIndent___closed__3;
lean_object* l_Lean_Parser_Term_liftMethod___closed__6;
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_liftMethod___closed__3;
lean_object* l_Lean_Parser_Term_doPat___closed__9;
lean_object* l_Lean_Parser_Term_doId;
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_doHave_formatter___closed__3;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doId_formatter___closed__3;
lean_object* l_Lean_Parser_Term_doLet___closed__5;
lean_object* l_Lean_Parser_Term_doExpr_formatter___closed__2;
extern lean_object* l_Lean_Parser_Tactic_indentedNonEmptySeq_formatter___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_optType___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_formatter(lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_doHave___closed__2;
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doPat___closed__1;
extern lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_doAssign___closed__3;
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr_formatter___closed__1;
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1;
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__9;
lean_object* l_Lean_Parser_Term_doHave___closed__1;
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__7;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeq_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doSeq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_leftArrow;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__9;
lean_object* l_Lean_Parser_Term_ident___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_doPat___closed__10;
extern lean_object* l_Lean_Parser_Tactic_indentedNonEmptySeq___closed__2;
lean_object* l_Lean_Parser_Term_doExpr___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqIndent;
lean_object* l_Lean_Parser_Term_doSeqIndent___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__4;
lean_object* l_Lean_Parser_Term_do___closed__7;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__6;
extern lean_object* l_Lean_Parser_Term_emptyC_formatter___closed__3;
extern lean_object* l_Lean_Parser_Term_haveDecl;
lean_object* l_Lean_Parser_Term_doHave___closed__4;
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer___closed__3;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Term_doExpr_formatter___closed__5;
lean_object* l___regBuiltin_Lean_Parser_Term_do_formatter(lean_object*);
lean_object* l_Lean_Parser_Term_doPat_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__7;
lean_object* l_Lean_Parser_Term_do_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_doElemParser_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doHave___elambda__1___closed__1;
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doSeq___closed__3;
lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__4;
lean_object* l_Lean_Parser_Term_doId___closed__7;
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doId_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4;
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__9;
extern lean_object* l_Lean_Parser_Term_have___closed__1;
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_emptyC___closed__3;
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__3;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__9;
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__7;
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_Term_let_formatter___closed__3;
lean_object* l_Lean_Parser_Term_doLet___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1___closed__5;
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3;
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__5;
lean_object* l_Lean_Parser_Term_doHave___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_unicodeSymbolFn___closed__1;
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__6;
lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_doId_formatter___closed__6;
lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5;
lean_object* l_Lean_Parser_Term_doHave___closed__3;
lean_object* l_Lean_Parser_Term_doExpr_formatter___closed__4;
lean_object* l_Lean_Parser_Term_doAssign___closed__2;
lean_object* l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1;
lean_object* l_Lean_Parser_Term_do_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Term_doSeq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__6;
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1;
lean_object* l_Lean_Parser_Term_doLet___closed__1;
lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_typeAscription___closed__2;
lean_object* l_Lean_Parser_Term_doHave___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_doHave___closed__5;
lean_object* l_Lean_Parser_Term_liftMethod_formatter___closed__4;
lean_object* l_Lean_Parser_Term_doLet___closed__4;
lean_object* l_Lean_Parser_Term_leftArrow___closed__2;
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_object* l_Lean_Parser_Term_doHave___closed__6;
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__5;
lean_object* l_Lean_Parser_Term_doLet___closed__2;
lean_object* l_Lean_Parser_Term_doId_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2;
lean_object* l_Lean_Parser_Term_doId_formatter___closed__1;
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__8;
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5;
extern lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__1;
extern lean_object* l_Lean_Parser_Term_have_formatter___closed__4;
lean_object* l_Lean_Parser_Term_leftArrow___closed__1;
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__6;
lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__2;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do_formatter___closed__2;
lean_object* l_Lean_Parser_doElemParser_formatter___boxed(lean_object*);
lean_object* l_Lean_Parser_Term_doPat_formatter___closed__3;
lean_object* l_Lean_Parser_Term_doId___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doLet_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doLet_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__4;
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1;
lean_object* l_Lean_Parser_Term_liftMethod_formatter___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_doAssign(lean_object*);
lean_object* l_Lean_Parser_Term_doHave;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do___elambda__1___closed__5;
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do_formatter___closed__1;
lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6;
lean_object* l_Lean_Parser_Term_doAssign_formatter___closed__3;
lean_object* l_Lean_Parser_Term_leftArrow_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_doSeqBracketed___closed__7;
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2;
lean_object* l_Lean_Parser_Term_doExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Parser_Term_doExpr___closed__7;
lean_object* l_Lean_Parser_Term_do___closed__5;
lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doPat___closed__5;
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doHave_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_haveDecl___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Parser_inhabited___closed__1;
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_formatter(lean_object*);
lean_object* l_Lean_Parser_Term_liftMethod_formatter___closed__2;
lean_object* l_Lean_Parser_Term_doSeqBracketed;
lean_object* l_Lean_Parser_Term_doLet;
extern lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_object* l_Lean_Parser_Term_doExpr;
lean_object* l_Lean_Parser_Term_doHave___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doAssign;
lean_object* l_Lean_Parser_Term_doExpr___closed__3;
lean_object* l_Lean_Parser_Term_doId___closed__6;
lean_object* l_Lean_Parser_Term_doAssign___closed__1;
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__7;
lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_do_parenthesizer___closed__4;
extern lean_object* l_Lean_Parser_Term_emptyC_formatter___closed__4;
lean_object* l_Lean_Parser_Term_liftMethod___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Term_doLet(lean_object*);
lean_object* l_Lean_Parser_Term_do_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doExpr___closed__5;
lean_object* l_Lean_Parser_Term_doPat_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_doHave___elambda__1(lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Term_ident_formatter___closed__1;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regDoElemParserAttribute(lean_object*);
lean_object* l_Lean_Parser_Term_do_parenthesizer___closed__2;
extern lean_object* l_Lean_Parser_Tactic_indentedNonEmptySeq_formatter___lambda__1___closed__4;
lean_object* l_Lean_Parser_Term_doLet_formatter___closed__2;
extern lean_object* l_Lean_Parser_Term_ident;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
lean_object* l_Lean_Parser_Term_liftMethod_formatter___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_doLet_formatter___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Term_doExpr(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinDoElemParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doElem");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinDoElemParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_regDoElemParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doElemParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regDoElemParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regDoElemParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regDoElemParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regDoElemParserAttribute___closed__2;
x_3 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_doElemParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ← ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <- ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__5;
x_2 = l_Lean_Parser_unicodeSymbolFn___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__6;
x_2 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_leftArrow___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__2;
x_4 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__4;
x_5 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__9;
x_6 = l_Lean_Parser_unicodeSymbolFnAux(x_3, x_4, x_5, x_1, x_2);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__4;
x_3 = l_Lean_Parser_unicodeSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_leftArrow___closed__1;
x_2 = l_Lean_Parser_Term_leftArrow___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_leftArrow() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_leftArrow___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("liftMethod");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_liftMethod___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_14 = l_Lean_Parser_categoryParser___elambda__1(x_13, x_6, x_1, x_11);
x_15 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_1);
x_17 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_11, x_17, x_10);
return x_18;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_1);
x_22 = lean_apply_2(x_4, x_1, x_2);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_25, x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_21);
x_27 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean_dec(x_20);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Parser_checkPrecFn(x_28, x_1, x_27);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
lean_inc(x_1);
x_33 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_29);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_36 = l_Lean_Parser_categoryParser___elambda__1(x_35, x_28, x_1, x_33);
x_37 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_32);
x_39 = 1;
x_40 = l_Lean_Parser_mergeOrElseErrors(x_38, x_24, x_21, x_39);
lean_dec(x_21);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_1);
x_41 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_33, x_41, x_32);
x_43 = 1;
x_44 = l_Lean_Parser_mergeOrElseErrors(x_42, x_24, x_21, x_43);
lean_dec(x_21);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_1);
x_45 = 1;
x_46 = l_Lean_Parser_mergeOrElseErrors(x_29, x_24, x_21, x_45);
lean_dec(x_21);
return x_46;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_leftArrow;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_typeAscription___closed__2;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_liftMethod___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_liftMethod___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_liftMethod___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_liftMethod___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_liftMethod___closed__4;
x_2 = l_Lean_Parser_Term_liftMethod___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_liftMethod___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_liftMethod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_3 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_liftMethod;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_leftArrow___elambda__1___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_leftArrow_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_liftMethod_formatter___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_Term_liftMethod_formatter___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_liftMethod_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_liftMethod_formatter___closed__1;
x_7 = l_Lean_Parser_Term_liftMethod_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_liftMethod_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_Term_leftArrow_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Term_leftArrow_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_liftMethod_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("do-elements must be indented");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_8, 2);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_18 = l_Lean_Parser_categoryParser___elambda__1(x_16, x_17, x_6, x_7);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_38; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_array_get_size(x_20);
lean_dec(x_20);
lean_inc(x_6);
x_58 = l_Lean_Parser_tokenFn(x_6, x_18);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 2)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__1;
x_64 = lean_string_dec_eq(x_62, x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_21);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_58, x_65, x_21);
x_38 = x_66;
goto block_57;
}
else
{
x_38 = x_58;
goto block_57;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
x_67 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_21);
x_68 = l_Lean_Parser_ParserState_mkErrorsAt(x_58, x_67, x_21);
x_38 = x_68;
goto block_57;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_59);
x_69 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_21);
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_58, x_69, x_21);
x_38 = x_70;
goto block_57;
}
block_37:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_ctor_get(x_23, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_22);
lean_dec(x_21);
{
uint8_t _tmp_4 = x_3;
lean_object* _tmp_6 = x_23;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_2);
x_29 = l_Lean_Parser_ParserState_restore(x_23, x_22, x_21);
lean_dec(x_22);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_4);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_2);
x_32 = l_Array_shrink___main___rarg(x_24, x_22);
lean_inc(x_21);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
x_34 = l_Lean_Parser_ParserState_restore(x_33, x_22, x_21);
lean_dec(x_22);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_4);
return x_36;
}
}
block_57:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = l_Lean_FileMap_toPosition(x_41, x_42);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_nat_dec_le(x_12, x_44);
lean_dec(x_44);
lean_dec(x_12);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1;
x_47 = l_Lean_Parser_ParserState_mkError(x_38, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
x_23 = x_47;
x_24 = x_48;
x_25 = x_49;
x_26 = x_50;
goto block_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 3);
lean_inc(x_53);
x_23 = x_38;
x_24 = x_51;
x_25 = x_52;
x_26 = x_53;
goto block_37;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_12);
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_38, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 3);
lean_inc(x_56);
x_23 = x_38;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
goto block_37;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_71 = lean_ctor_get(x_18, 1);
lean_inc(x_71);
x_72 = lean_nat_dec_lt(x_15, x_71);
lean_dec(x_71);
if (x_72 == 0)
{
if (x_5 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_15);
lean_dec(x_14);
x_73 = lean_box(0);
x_74 = l_Lean_Parser_ParserState_pushSyntax(x_18, x_73);
x_75 = l_Lean_nullKind;
x_76 = l_Lean_Parser_ParserState_mkNode(x_74, x_75, x_4);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = l_Lean_Parser_ParserState_restore(x_18, x_14, x_15);
lean_dec(x_14);
x_78 = l_Lean_nullKind;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_4);
return x_79;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2(x_1, x_2, x_3, x_7, x_8, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1(x_1, x_2, x_3, x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqIndent___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_indentedNonEmptySeq___closed__3;
x_4 = l_Lean_Parser_sepBy1Info(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqIndent___closed__2;
x_2 = l_Lean_Parser_Term_doSeqIndent___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doSeqIndent___closed__4;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_11 = l_Lean_Parser_categoryParser___elambda__1(x_9, x_10, x_4, x_5);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_4);
x_23 = l_Lean_Parser_tokenFn(x_4, x_11);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 2)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__1;
x_29 = lean_string_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_15);
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_23, x_30, x_15);
x_16 = x_31;
goto block_22;
}
else
{
x_16 = x_23;
goto block_22;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_32 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_15);
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_23, x_32, x_15);
x_16 = x_33;
goto block_22;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_34 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Tactic_indentedNonEmptySeq___spec__2___closed__5;
lean_inc(x_15);
x_35 = l_Lean_Parser_ParserState_mkErrorsAt(x_23, x_34, x_15);
x_16 = x_35;
goto block_22;
}
block_22:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
{
uint8_t _tmp_2 = x_1;
lean_object* _tmp_4 = x_16;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_4);
x_19 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_20 = l_Lean_nullKind;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_2);
return x_21;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_4);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_8, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
if (x_3 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_38);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_2);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Parser_ParserState_restore(x_11, x_7, x_8);
lean_dec(x_7);
x_43 = l_Lean_nullKind;
x_44 = l_Lean_Parser_ParserState_mkNode(x_42, x_43, x_2);
return x_44;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_11;
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqBracketed");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doSeqBracketed___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_1);
x_44 = l_Lean_Parser_tokenFn(x_1, x_7);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 2)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Parser_Term_emptyC___elambda__1___closed__7;
x_50 = lean_string_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_44, x_51, x_43);
x_11 = x_52;
goto block_42;
}
else
{
lean_dec(x_43);
x_11 = x_44;
goto block_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
x_53 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_44, x_53, x_43);
x_11 = x_54;
goto block_42;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
x_55 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_56 = l_Lean_Parser_ParserState_mkErrorsAt(x_44, x_55, x_43);
x_11 = x_56;
goto block_42;
}
block_42:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
lean_inc(x_1);
x_14 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1(x_13, x_1, x_11);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_Parser_tokenFn(x_1, x_14);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Parser_Term_emptyC___elambda__1___closed__8;
x_23 = lean_string_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_24, x_16);
x_26 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_28 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_17, x_28, x_10);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_30 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_30, x_16);
x_32 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_10);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
x_34 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_35 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_34, x_16);
x_36 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_10);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_1);
x_38 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_14, x_38, x_10);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_1);
x_40 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_11, x_40, x_10);
return x_41;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_inc(x_1);
x_60 = lean_apply_2(x_4, x_1, x_2);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_nat_dec_eq(x_63, x_59);
lean_dec(x_63);
if (x_64 == 0)
{
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_59);
x_65 = l_Lean_Parser_ParserState_restore(x_60, x_58, x_59);
lean_dec(x_58);
x_66 = lean_unsigned_to_nat(1024u);
x_67 = l_Lean_Parser_checkPrecFn(x_66, x_1, x_65);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_array_get_size(x_69);
lean_dec(x_69);
x_110 = lean_ctor_get(x_67, 1);
lean_inc(x_110);
lean_inc(x_1);
x_111 = l_Lean_Parser_tokenFn(x_1, x_67);
x_112 = lean_ctor_get(x_111, 3);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 2)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Parser_Term_emptyC___elambda__1___closed__7;
x_117 = lean_string_dec_eq(x_115, x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_119 = l_Lean_Parser_ParserState_mkErrorsAt(x_111, x_118, x_110);
x_71 = x_119;
goto block_109;
}
else
{
lean_dec(x_110);
x_71 = x_111;
goto block_109;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_114);
x_120 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_121 = l_Lean_Parser_ParserState_mkErrorsAt(x_111, x_120, x_110);
x_71 = x_121;
goto block_109;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_112);
x_122 = l_Lean_Parser_Term_emptyC___elambda__1___closed__14;
x_123 = l_Lean_Parser_ParserState_mkErrorsAt(x_111, x_122, x_110);
x_71 = x_123;
goto block_109;
}
block_109:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_73 = 1;
lean_inc(x_1);
x_74 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1(x_73, x_1, x_71);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = l_Lean_Parser_tokenFn(x_1, x_74);
x_78 = lean_ctor_get(x_77, 3);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_79);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 2)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Parser_Term_emptyC___elambda__1___closed__8;
x_83 = lean_string_dec_eq(x_81, x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_77, x_84, x_76);
x_86 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_70);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_62, x_59, x_73);
lean_dec(x_59);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
x_89 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_90 = l_Lean_Parser_ParserState_mkNode(x_77, x_89, x_70);
x_91 = l_Lean_Parser_mergeOrElseErrors(x_90, x_62, x_59, x_73);
lean_dec(x_59);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_80);
x_92 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_93 = l_Lean_Parser_ParserState_mkErrorsAt(x_77, x_92, x_76);
x_94 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_95 = l_Lean_Parser_ParserState_mkNode(x_93, x_94, x_70);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_62, x_59, x_73);
lean_dec(x_59);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_78);
x_97 = l_Lean_Parser_Term_emptyC___elambda__1___closed__11;
x_98 = l_Lean_Parser_ParserState_mkErrorsAt(x_77, x_97, x_76);
x_99 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_100 = l_Lean_Parser_ParserState_mkNode(x_98, x_99, x_70);
x_101 = l_Lean_Parser_mergeOrElseErrors(x_100, x_62, x_59, x_73);
lean_dec(x_59);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_75);
lean_dec(x_1);
x_102 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_103 = l_Lean_Parser_ParserState_mkNode(x_74, x_102, x_70);
x_104 = l_Lean_Parser_mergeOrElseErrors(x_103, x_62, x_59, x_73);
lean_dec(x_59);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
lean_dec(x_72);
lean_dec(x_1);
x_105 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_106 = l_Lean_Parser_ParserState_mkNode(x_71, x_105, x_70);
x_107 = 1;
x_108 = l_Lean_Parser_mergeOrElseErrors(x_106, x_62, x_59, x_107);
lean_dec(x_59);
return x_108;
}
}
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_68);
lean_dec(x_1);
x_124 = 1;
x_125 = l_Lean_Parser_mergeOrElseErrors(x_67, x_62, x_59, x_124);
lean_dec(x_59);
return x_125;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqIndent___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_indentedNonEmptySeq___closed__2;
x_4 = l_Lean_Parser_sepBy1Info(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___closed__1;
x_2 = l_Lean_Parser_Term_emptyC___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_emptyC___closed__2;
x_2 = l_Lean_Parser_Term_doSeqBracketed___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doSeqBracketed___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doSeqBracketed___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doSeqBracketed___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___closed__6;
x_2 = l_Lean_Parser_Term_doSeqBracketed___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___closed__8;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__2(x_6, x_2, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqBracketed___elambda__1___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_Term_doSeq___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Parser_Term_doSeqBracketed___elambda__1(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_9, x_5);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_5);
x_11 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_12 = 0;
lean_inc(x_11);
lean_inc(x_1);
x_13 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__1(x_1, x_11, x_12, x_1, x_11);
lean_dec(x_1);
x_14 = 1;
x_15 = l_Lean_Parser_mergeOrElseErrors(x_13, x_8, x_5, x_14);
lean_dec(x_5);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doSeqBracketed;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doSeqIndent;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeq___closed__1;
x_2 = l_Lean_Parser_Term_doSeq___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doSeq___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doLet");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doLet___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doLet___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doLet___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Parser_Term_letDecl;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Term_doLet___elambda__1___closed__4;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = l_Lean_Parser_checkPrecFn(x_8, x_1, x_2);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_Parser_tokenFn(x_1, x_9);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Parser_Term_let___elambda__1___closed__6;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_29, x_21);
x_13 = x_30;
goto block_20;
}
else
{
lean_dec(x_21);
x_13 = x_22;
goto block_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_31 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_32 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_31, x_21);
x_13 = x_32;
goto block_20;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
x_33 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_34 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_33, x_21);
x_13 = x_34;
goto block_20;
}
block_20:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_apply_2(x_4, x_1, x_13);
x_16 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_18 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_13, x_18, x_12);
return x_19;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_1);
x_38 = lean_apply_2(x_6, x_1, x_2);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_nat_dec_eq(x_41, x_37);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc(x_37);
x_43 = l_Lean_Parser_ParserState_restore(x_38, x_36, x_37);
lean_dec(x_36);
x_44 = lean_unsigned_to_nat(1024u);
x_45 = l_Lean_Parser_checkPrecFn(x_44, x_1, x_43);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_inc(x_1);
x_62 = l_Lean_Parser_tokenFn(x_1, x_45);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_64);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 2)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Parser_Term_let___elambda__1___closed__6;
x_68 = lean_string_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_69, x_61);
x_49 = x_70;
goto block_60;
}
else
{
lean_dec(x_61);
x_49 = x_62;
goto block_60;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_71 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_71, x_61);
x_49 = x_72;
goto block_60;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
x_73 = l_Lean_Parser_Term_let___elambda__1___closed__9;
x_74 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_73, x_61);
x_49 = x_74;
goto block_60;
}
block_60:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_apply_2(x_4, x_1, x_49);
x_52 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_53 = l_Lean_Parser_ParserState_mkNode(x_51, x_52, x_48);
x_54 = 1;
x_55 = l_Lean_Parser_mergeOrElseErrors(x_53, x_40, x_37, x_54);
lean_dec(x_37);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_1);
x_56 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_57 = l_Lean_Parser_ParserState_mkNode(x_49, x_56, x_48);
x_58 = 1;
x_59 = l_Lean_Parser_mergeOrElseErrors(x_57, x_40, x_37, x_58);
lean_dec(x_37);
return x_59;
}
}
}
else
{
uint8_t x_75; lean_object* x_76; 
lean_dec(x_46);
lean_dec(x_4);
lean_dec(x_1);
x_75 = 1;
x_76 = l_Lean_Parser_mergeOrElseErrors(x_45, x_40, x_37, x_75);
lean_dec(x_37);
return x_76;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_letDecl;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_let___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doLet___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doLet___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doLet___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLet___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doLet___closed__4;
x_2 = l_Lean_Parser_Term_doLet___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doLet___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_doLet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_3 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_doLet;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doLet___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_let_formatter___closed__2;
x_2 = l_Lean_Parser_Term_let_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doLet_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doLet_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doLet_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doLet_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLet_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Term_let_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doLet_parenthesizer___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doLet_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doLet_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doLet_parenthesizer___closed__3;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLet_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doId");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doId___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doId___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doId___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_doId___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_29 = l_Lean_Parser_Term_ident___elambda__1(x_1, x_7);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_1);
x_31 = l_Lean_Parser_Term_optType___elambda__1(x_1, x_29);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_1);
x_33 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 3);
lean_inc(x_36);
x_12 = x_33;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
goto block_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 3);
lean_inc(x_39);
x_12 = x_31;
x_13 = x_37;
x_14 = x_38;
x_15 = x_39;
goto block_28;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_29, 3);
lean_inc(x_42);
x_12 = x_29;
x_13 = x_40;
x_14 = x_41;
x_15 = x_42;
goto block_28;
}
block_28:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Parser_categoryParser___elambda__1(x_17, x_18, x_1, x_12);
x_20 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_1);
x_22 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_12, x_22, x_11);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_1);
x_24 = l_Array_shrink___main___rarg(x_13, x_11);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_15);
x_26 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_11);
return x_27;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_inc(x_1);
x_46 = lean_apply_2(x_4, x_1, x_2);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_nat_dec_eq(x_49, x_45);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_45);
x_51 = l_Lean_Parser_ParserState_restore(x_46, x_44, x_45);
lean_dec(x_44);
x_52 = lean_unsigned_to_nat(1024u);
x_53 = l_Lean_Parser_checkPrecFn(x_52, x_1, x_51);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_81; lean_object* x_82; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_array_get_size(x_55);
lean_dec(x_55);
lean_inc(x_1);
x_81 = l_Lean_Parser_Term_ident___elambda__1(x_1, x_53);
x_82 = lean_ctor_get(x_81, 3);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_inc(x_1);
x_83 = l_Lean_Parser_Term_optType___elambda__1(x_1, x_81);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc(x_1);
x_85 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_88;
goto block_80;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 3);
lean_inc(x_91);
x_58 = x_83;
x_59 = x_89;
x_60 = x_90;
x_61 = x_91;
goto block_80;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 3);
lean_inc(x_94);
x_58 = x_81;
x_59 = x_92;
x_60 = x_93;
x_61 = x_94;
goto block_80;
}
block_80:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_56);
x_62 = lean_ctor_get(x_58, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_63 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Parser_categoryParser___elambda__1(x_63, x_64, x_1, x_58);
x_66 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_67 = l_Lean_Parser_ParserState_mkNode(x_65, x_66, x_57);
x_68 = 1;
x_69 = l_Lean_Parser_mergeOrElseErrors(x_67, x_48, x_45, x_68);
lean_dec(x_45);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
lean_dec(x_62);
lean_dec(x_1);
x_70 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_71 = l_Lean_Parser_ParserState_mkNode(x_58, x_70, x_57);
x_72 = 1;
x_73 = l_Lean_Parser_mergeOrElseErrors(x_71, x_48, x_45, x_72);
lean_dec(x_45);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_1);
x_74 = l_Array_shrink___main___rarg(x_59, x_57);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_75, 2, x_60);
lean_ctor_set(x_75, 3, x_61);
x_76 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_77 = l_Lean_Parser_ParserState_mkNode(x_75, x_76, x_57);
x_78 = 1;
x_79 = l_Lean_Parser_mergeOrElseErrors(x_77, x_48, x_45, x_78);
lean_dec(x_45);
return x_79;
}
}
}
else
{
uint8_t x_95; lean_object* x_96; 
lean_dec(x_54);
lean_dec(x_1);
x_95 = 1;
x_96 = l_Lean_Parser_mergeOrElseErrors(x_53, x_48, x_45, x_95);
lean_dec(x_45);
return x_96;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_optType;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_leftArrow;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doId___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doId___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doId___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doId___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doId___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doId___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doId___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doId___closed__6;
x_2 = l_Lean_Parser_Term_doId___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doId___closed__8;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doPat");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doPat___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doPat___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" | ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_doPat___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_doPat___elambda__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_doPat___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_doPat___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_9);
lean_dec(x_9);
x_70 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_71 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_72 = l_Lean_Parser_categoryParser___elambda__1(x_70, x_71, x_1, x_7);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_inc(x_1);
x_74 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_72);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_dec(x_10);
x_12 = x_74;
goto block_69;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_dec(x_79);
x_80 = l_Array_shrink___main___rarg(x_77, x_11);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 0, x_80);
x_12 = x_74;
goto block_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_74, 0);
x_82 = lean_ctor_get(x_74, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_74);
x_83 = l_Array_shrink___main___rarg(x_81, x_11);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_10);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_75);
x_12 = x_84;
goto block_69;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_73);
x_85 = lean_ctor_get(x_72, 3);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_10);
x_12 = x_72;
goto block_69;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_72);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_72, 0);
x_88 = lean_ctor_get(x_72, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_dec(x_89);
x_90 = l_Array_shrink___main___rarg(x_87, x_11);
lean_ctor_set(x_72, 1, x_10);
lean_ctor_set(x_72, 0, x_90);
x_12 = x_72;
goto block_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_72, 0);
x_92 = lean_ctor_get(x_72, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_72);
x_93 = l_Array_shrink___main___rarg(x_91, x_11);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_85);
x_12 = x_94;
goto block_69;
}
}
}
block_69:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_52; lean_object* x_53; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_1);
x_52 = l_Lean_Parser_tokenFn(x_1, x_16);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_54);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 2)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Parser_Term_doPat___elambda__1___closed__6;
x_58 = lean_string_dec_eq(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_20);
x_60 = l_Lean_Parser_ParserState_mkErrorsAt(x_52, x_59, x_20);
x_21 = x_60;
goto block_51;
}
else
{
x_21 = x_52;
goto block_51;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
x_61 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_20);
x_62 = l_Lean_Parser_ParserState_mkErrorsAt(x_52, x_61, x_20);
x_21 = x_62;
goto block_51;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
x_63 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_20);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_52, x_63, x_20);
x_21 = x_64;
goto block_51;
}
block_51:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_21);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_23, x_25, x_19);
x_27 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_11);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
x_30 = lean_nat_dec_eq(x_29, x_20);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_23, x_31, x_19);
x_33 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Lean_Parser_ParserState_restore(x_23, x_19, x_20);
x_36 = l_Lean_nullKind;
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_19);
x_38 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_11);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_22);
lean_dec(x_1);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
x_41 = lean_nat_dec_eq(x_40, x_20);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_20);
x_42 = l_Lean_nullKind;
x_43 = l_Lean_Parser_ParserState_mkNode(x_21, x_42, x_19);
x_44 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_11);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = l_Lean_Parser_ParserState_restore(x_21, x_19, x_20);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_19);
x_49 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_11);
return x_50;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_17);
lean_dec(x_1);
x_65 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_66 = l_Lean_Parser_ParserState_mkNode(x_16, x_65, x_11);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
lean_dec(x_1);
x_67 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_68 = l_Lean_Parser_ParserState_mkNode(x_12, x_67, x_11);
return x_68;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc(x_95);
x_96 = lean_array_get_size(x_95);
lean_dec(x_95);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_inc(x_1);
x_98 = lean_apply_2(x_4, x_1, x_2);
x_99 = lean_ctor_get(x_98, 3);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
x_102 = lean_nat_dec_eq(x_101, x_97);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_inc(x_97);
x_103 = l_Lean_Parser_ParserState_restore(x_98, x_96, x_97);
lean_dec(x_96);
x_104 = lean_unsigned_to_nat(1024u);
x_105 = l_Lean_Parser_checkPrecFn(x_104, x_1, x_103);
x_106 = lean_ctor_get(x_105, 3);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
x_109 = lean_array_get_size(x_107);
lean_dec(x_107);
x_182 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_183 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_184 = l_Lean_Parser_categoryParser___elambda__1(x_182, x_183, x_1, x_105);
x_185 = lean_ctor_get(x_184, 3);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_inc(x_1);
x_186 = l_Lean_Parser_Term_leftArrow___elambda__1(x_1, x_184);
x_187 = lean_ctor_get(x_186, 3);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_dec(x_108);
x_110 = x_186;
goto block_181;
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_186);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_186, 0);
x_190 = lean_ctor_get(x_186, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_186, 1);
lean_dec(x_191);
x_192 = l_Array_shrink___main___rarg(x_189, x_109);
lean_ctor_set(x_186, 1, x_108);
lean_ctor_set(x_186, 0, x_192);
x_110 = x_186;
goto block_181;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_186, 0);
x_194 = lean_ctor_get(x_186, 2);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_186);
x_195 = l_Array_shrink___main___rarg(x_193, x_109);
x_196 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_108);
lean_ctor_set(x_196, 2, x_194);
lean_ctor_set(x_196, 3, x_187);
x_110 = x_196;
goto block_181;
}
}
}
else
{
lean_object* x_197; 
lean_dec(x_185);
x_197 = lean_ctor_get(x_184, 3);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_dec(x_108);
x_110 = x_184;
goto block_181;
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_184, 0);
x_200 = lean_ctor_get(x_184, 3);
lean_dec(x_200);
x_201 = lean_ctor_get(x_184, 1);
lean_dec(x_201);
x_202 = l_Array_shrink___main___rarg(x_199, x_109);
lean_ctor_set(x_184, 1, x_108);
lean_ctor_set(x_184, 0, x_202);
x_110 = x_184;
goto block_181;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_184, 0);
x_204 = lean_ctor_get(x_184, 2);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_184);
x_205 = l_Array_shrink___main___rarg(x_203, x_109);
x_206 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_108);
lean_ctor_set(x_206, 2, x_204);
lean_ctor_set(x_206, 3, x_197);
x_110 = x_206;
goto block_181;
}
}
}
block_181:
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_113 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_114 = l_Lean_Parser_categoryParser___elambda__1(x_112, x_113, x_1, x_110);
x_115 = lean_ctor_get(x_114, 3);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_160; lean_object* x_161; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_array_get_size(x_116);
lean_dec(x_116);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_inc(x_1);
x_160 = l_Lean_Parser_tokenFn(x_1, x_114);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_162);
lean_dec(x_162);
if (lean_obj_tag(x_163) == 2)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l_Lean_Parser_Term_doPat___elambda__1___closed__6;
x_166 = lean_string_dec_eq(x_164, x_165);
lean_dec(x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_118);
x_168 = l_Lean_Parser_ParserState_mkErrorsAt(x_160, x_167, x_118);
x_119 = x_168;
goto block_159;
}
else
{
x_119 = x_160;
goto block_159;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_163);
x_169 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_118);
x_170 = l_Lean_Parser_ParserState_mkErrorsAt(x_160, x_169, x_118);
x_119 = x_170;
goto block_159;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_161);
x_171 = l_Lean_Parser_Term_doPat___elambda__1___closed__9;
lean_inc(x_118);
x_172 = l_Lean_Parser_ParserState_mkErrorsAt(x_160, x_171, x_118);
x_119 = x_172;
goto block_159;
}
block_159:
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 3);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_Parser_categoryParser___elambda__1(x_112, x_113, x_1, x_119);
x_122 = lean_ctor_get(x_121, 3);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
lean_dec(x_118);
x_123 = l_Lean_nullKind;
x_124 = l_Lean_Parser_ParserState_mkNode(x_121, x_123, x_117);
x_125 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_126 = l_Lean_Parser_ParserState_mkNode(x_124, x_125, x_109);
x_127 = 1;
x_128 = l_Lean_Parser_mergeOrElseErrors(x_126, x_100, x_97, x_127);
lean_dec(x_97);
return x_128;
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_122);
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
x_130 = lean_nat_dec_eq(x_129, x_118);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
lean_dec(x_118);
x_131 = l_Lean_nullKind;
x_132 = l_Lean_Parser_ParserState_mkNode(x_121, x_131, x_117);
x_133 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_132, x_133, x_109);
x_135 = 1;
x_136 = l_Lean_Parser_mergeOrElseErrors(x_134, x_100, x_97, x_135);
lean_dec(x_97);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_137 = l_Lean_Parser_ParserState_restore(x_121, x_117, x_118);
x_138 = l_Lean_nullKind;
x_139 = l_Lean_Parser_ParserState_mkNode(x_137, x_138, x_117);
x_140 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_141 = l_Lean_Parser_ParserState_mkNode(x_139, x_140, x_109);
x_142 = 1;
x_143 = l_Lean_Parser_mergeOrElseErrors(x_141, x_100, x_97, x_142);
lean_dec(x_97);
return x_143;
}
}
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_120);
lean_dec(x_1);
x_144 = lean_ctor_get(x_119, 1);
lean_inc(x_144);
x_145 = lean_nat_dec_eq(x_144, x_118);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
lean_dec(x_118);
x_146 = l_Lean_nullKind;
x_147 = l_Lean_Parser_ParserState_mkNode(x_119, x_146, x_117);
x_148 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_149 = l_Lean_Parser_ParserState_mkNode(x_147, x_148, x_109);
x_150 = 1;
x_151 = l_Lean_Parser_mergeOrElseErrors(x_149, x_100, x_97, x_150);
lean_dec(x_97);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_152 = l_Lean_Parser_ParserState_restore(x_119, x_117, x_118);
x_153 = l_Lean_nullKind;
x_154 = l_Lean_Parser_ParserState_mkNode(x_152, x_153, x_117);
x_155 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_156 = l_Lean_Parser_ParserState_mkNode(x_154, x_155, x_109);
x_157 = 1;
x_158 = l_Lean_Parser_mergeOrElseErrors(x_156, x_100, x_97, x_157);
lean_dec(x_97);
return x_158;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
lean_dec(x_115);
lean_dec(x_1);
x_173 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_174 = l_Lean_Parser_ParserState_mkNode(x_114, x_173, x_109);
x_175 = 1;
x_176 = l_Lean_Parser_mergeOrElseErrors(x_174, x_100, x_97, x_175);
lean_dec(x_97);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
lean_dec(x_111);
lean_dec(x_1);
x_177 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_178 = l_Lean_Parser_ParserState_mkNode(x_110, x_177, x_109);
x_179 = 1;
x_180 = l_Lean_Parser_mergeOrElseErrors(x_178, x_100, x_97, x_179);
lean_dec(x_97);
return x_180;
}
}
}
else
{
uint8_t x_207; lean_object* x_208; 
lean_dec(x_106);
lean_dec(x_1);
x_207 = 1;
x_208 = l_Lean_Parser_mergeOrElseErrors(x_105, x_100, x_97, x_207);
lean_dec(x_97);
return x_208;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_leftArrow;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__6;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doPat___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat___closed__3;
x_2 = l_Lean_Parser_optionaInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doPat___closed__4;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat___closed__1;
x_2 = l_Lean_Parser_Term_doPat___closed__5;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doPat___closed__6;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doPat___closed__7;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doPat___closed__8;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPat___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat___closed__9;
x_2 = l_Lean_Parser_Term_doPat___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doPat___closed__11;
return x_1;
}
}
lean_object* l_Lean_Parser_Term_doAssign___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_24; lean_object* x_25; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l_Lean_Parser_tokenFn(x_1, x_2);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 2)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Parser_Term_let___elambda__1___closed__6;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_5);
x_32 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_31, x_5);
x_6 = x_32;
goto block_23;
}
else
{
x_6 = x_24;
goto block_23;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_33 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_5);
x_34 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_33, x_5);
x_6 = x_34;
goto block_23;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_35 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_5);
x_36 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_35, x_5);
x_6 = x_36;
goto block_23;
}
block_23:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_9 = l_Lean_Parser_notFollowedByFn___closed__1;
x_10 = l_Lean_Parser_ParserState_mkError(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_inc(x_5);
x_11 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Parser_Term_doId___elambda__1(x_1, x_11);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_17, x_5);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_inc(x_5);
x_19 = l_Lean_Parser_ParserState_restore(x_14, x_13, x_5);
lean_dec(x_13);
x_20 = l_Lean_Parser_Term_doPat___elambda__1(x_1, x_19);
x_21 = 1;
x_22 = l_Lean_Parser_mergeOrElseErrors(x_20, x_16, x_5, x_21);
lean_dec(x_5);
return x_22;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doId;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doPat;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_doAssign___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doAssign___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign___closed__2;
x_2 = l_Lean_Parser_Term_doAssign___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doAssign___closed__4;
return x_1;
}
}
lean_object* _init_l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doAssign");
return x_1;
}
}
lean_object* _init_l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_doAssign(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_3 = l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_doAssign;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doId___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_subtype_formatter___closed__6;
x_2 = l_Lean_Parser_Term_liftMethod_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Term_ident_formatter___closed__1;
x_2 = l_Lean_Parser_Term_doId_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doId_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_try_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doId_formatter___closed__4;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doId_formatter___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doId_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doId_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doId_formatter___closed__6;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doPat___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_2 = l_Lean_Parser_Term_liftMethod_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_try_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat_formatter___closed__4;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_optional_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_2 = l_Lean_Parser_Term_doPat_formatter___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat_formatter___closed__3;
x_2 = l_Lean_Parser_Term_doPat_formatter___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doPat_formatter___closed__8;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doPat_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doPat_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doPat_formatter___closed__9;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_let_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doId_formatter), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPat_formatter), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign_formatter___closed__2;
x_2 = l_Lean_Parser_Term_doAssign_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_doAssign_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doAssign_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doAssign_formatter___closed__4;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doAssign_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_subtype_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Parser_Term_ident_parenthesizer___closed__1;
x_2 = l_Lean_Parser_Term_doId_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doId_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doId_parenthesizer___closed__4;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doId_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doId_parenthesizer___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doId_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doId_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doId_parenthesizer___closed__6;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_2 = l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doPat_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_2 = l_Lean_Parser_Term_structInst_parenthesizer___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doPat_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Term_doPat_parenthesizer___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doPat_parenthesizer___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doPat_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doPat_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doPat_parenthesizer___closed__6;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doId_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPat_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__2;
x_2 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_doAssign_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doAssign_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doHave");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doHave___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doHave___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doHave___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_doHave___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_1);
x_20 = l_Lean_Parser_tokenFn(x_1, x_7);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_Term_have___elambda__1___closed__6;
x_26 = lean_string_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_28 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_27, x_19);
x_11 = x_28;
goto block_18;
}
else
{
lean_dec(x_19);
x_11 = x_20;
goto block_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_29 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_29, x_19);
x_11 = x_30;
goto block_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_31 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_32 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_31, x_19);
x_11 = x_32;
goto block_18;
}
block_18:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Parser_Term_haveDecl___elambda__1(x_1, x_11);
x_14 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_13, x_14, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_11, x_16, x_10);
return x_17;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_apply_2(x_4, x_1, x_2);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_nat_dec_eq(x_39, x_35);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_35);
x_41 = l_Lean_Parser_ParserState_restore(x_36, x_34, x_35);
lean_dec(x_34);
x_42 = lean_unsigned_to_nat(1024u);
x_43 = l_Lean_Parser_checkPrecFn(x_42, x_1, x_41);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
lean_inc(x_1);
x_60 = l_Lean_Parser_tokenFn(x_1, x_43);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 2)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Parser_Term_have___elambda__1___closed__6;
x_66 = lean_string_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_68 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_67, x_59);
x_47 = x_68;
goto block_58;
}
else
{
lean_dec(x_59);
x_47 = x_60;
goto block_58;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
x_69 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_69, x_59);
x_47 = x_70;
goto block_58;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
x_71 = l_Lean_Parser_Term_have___elambda__1___closed__9;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_71, x_59);
x_47 = x_72;
goto block_58;
}
block_58:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_49 = l_Lean_Parser_Term_haveDecl___elambda__1(x_1, x_47);
x_50 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_46);
x_52 = 1;
x_53 = l_Lean_Parser_mergeOrElseErrors(x_51, x_38, x_35, x_52);
lean_dec(x_35);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_47, x_54, x_46);
x_56 = 1;
x_57 = l_Lean_Parser_mergeOrElseErrors(x_55, x_38, x_35, x_56);
lean_dec(x_35);
return x_57;
}
}
}
else
{
uint8_t x_73; lean_object* x_74; 
lean_dec(x_44);
lean_dec(x_1);
x_73 = 1;
x_74 = l_Lean_Parser_mergeOrElseErrors(x_43, x_38, x_35, x_73);
lean_dec(x_35);
return x_74;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_haveDecl;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_have___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doHave___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doHave___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doHave___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doHave___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doHave___closed__4;
x_2 = l_Lean_Parser_Term_doHave___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doHave___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_doHave(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_3 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_doHave;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doHave___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_have_formatter___closed__2;
x_2 = l_Lean_Parser_Term_have_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doHave_formatter___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doHave_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doHave_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doHave_formatter___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doHave_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Term_have_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doHave_parenthesizer___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doHave_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doHave_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doHave_parenthesizer___closed__3;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doHave_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Term_doHave___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doExpr");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_doExpr___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doExpr___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doExpr___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_doExpr___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_46; lean_object* x_47; lean_object* x_54; lean_object* x_55; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_1);
x_54 = l_Lean_Parser_tokenFn(x_1, x_7);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 2)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Parser_Term_let___elambda__1___closed__6;
x_60 = lean_string_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_46);
x_62 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_61, x_46);
x_47 = x_62;
goto block_53;
}
else
{
x_47 = x_54;
goto block_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_63 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_46);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_63, x_46);
x_47 = x_64;
goto block_53;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_65 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_46);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_65, x_46);
x_47 = x_66;
goto block_53;
}
block_45:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; lean_object* x_31; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_1);
x_30 = l_Lean_Parser_tokenFn(x_1, x_11);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 2)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Parser_Term_have___elambda__1___closed__6;
x_36 = lean_string_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_15);
x_38 = l_Lean_Parser_ParserState_mkErrorsAt(x_30, x_37, x_15);
x_16 = x_38;
goto block_29;
}
else
{
x_16 = x_30;
goto block_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_39 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_15);
x_40 = l_Lean_Parser_ParserState_mkErrorsAt(x_30, x_39, x_15);
x_16 = x_40;
goto block_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
x_41 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_15);
x_42 = l_Lean_Parser_ParserState_mkErrorsAt(x_30, x_41, x_15);
x_16 = x_42;
goto block_29;
}
block_29:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_19 = l_Lean_Parser_notFollowedByFn___closed__1;
x_20 = l_Lean_Parser_ParserState_mkError(x_18, x_19);
x_21 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_23 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_24 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Parser_categoryParser___elambda__1(x_24, x_25, x_1, x_23);
x_27 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_10);
return x_28;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_1);
x_43 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_44 = l_Lean_Parser_ParserState_mkNode(x_11, x_43, x_10);
return x_44;
}
}
block_53:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_Parser_ParserState_restore(x_47, x_10, x_46);
x_50 = l_Lean_Parser_notFollowedByFn___closed__1;
x_51 = l_Lean_Parser_ParserState_mkError(x_49, x_50);
x_11 = x_51;
goto block_45;
}
else
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = l_Lean_Parser_ParserState_restore(x_47, x_10, x_46);
x_11 = x_52;
goto block_45;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
lean_inc(x_1);
x_70 = lean_apply_2(x_4, x_1, x_2);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_1);
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_nat_dec_eq(x_73, x_69);
lean_dec(x_73);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_1);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_69);
x_75 = l_Lean_Parser_ParserState_restore(x_70, x_68, x_69);
lean_dec(x_68);
x_76 = lean_unsigned_to_nat(1024u);
x_77 = l_Lean_Parser_checkPrecFn(x_76, x_1, x_75);
x_78 = lean_ctor_get(x_77, 3);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_122; lean_object* x_123; lean_object* x_130; lean_object* x_131; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_array_get_size(x_79);
lean_dec(x_79);
x_122 = lean_ctor_get(x_77, 1);
lean_inc(x_122);
lean_inc(x_1);
x_130 = l_Lean_Parser_tokenFn(x_1, x_77);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_132);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 2)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = l_Lean_Parser_Term_let___elambda__1___closed__6;
x_136 = lean_string_dec_eq(x_134, x_135);
lean_dec(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_122);
x_138 = l_Lean_Parser_ParserState_mkErrorsAt(x_130, x_137, x_122);
x_123 = x_138;
goto block_129;
}
else
{
x_123 = x_130;
goto block_129;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_133);
x_139 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_122);
x_140 = l_Lean_Parser_ParserState_mkErrorsAt(x_130, x_139, x_122);
x_123 = x_140;
goto block_129;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_131);
x_141 = l_Lean_Parser_Term_let___elambda__1___closed__9;
lean_inc(x_122);
x_142 = l_Lean_Parser_ParserState_mkErrorsAt(x_130, x_141, x_122);
x_123 = x_142;
goto block_129;
}
block_121:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 3);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_104; lean_object* x_105; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_array_get_size(x_83);
lean_dec(x_83);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_inc(x_1);
x_104 = l_Lean_Parser_tokenFn(x_1, x_81);
x_105 = lean_ctor_get(x_104, 3);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_106);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 2)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Parser_Term_have___elambda__1___closed__6;
x_110 = lean_string_dec_eq(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_85);
x_112 = l_Lean_Parser_ParserState_mkErrorsAt(x_104, x_111, x_85);
x_86 = x_112;
goto block_103;
}
else
{
x_86 = x_104;
goto block_103;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_107);
x_113 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_85);
x_114 = l_Lean_Parser_ParserState_mkErrorsAt(x_104, x_113, x_85);
x_86 = x_114;
goto block_103;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_105);
x_115 = l_Lean_Parser_Term_have___elambda__1___closed__9;
lean_inc(x_85);
x_116 = l_Lean_Parser_ParserState_mkErrorsAt(x_104, x_115, x_85);
x_86 = x_116;
goto block_103;
}
block_103:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 3);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
lean_dec(x_1);
x_88 = l_Lean_Parser_ParserState_restore(x_86, x_84, x_85);
lean_dec(x_84);
x_89 = l_Lean_Parser_notFollowedByFn___closed__1;
x_90 = l_Lean_Parser_ParserState_mkError(x_88, x_89);
x_91 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_80);
x_93 = 1;
x_94 = l_Lean_Parser_mergeOrElseErrors(x_92, x_72, x_69, x_93);
lean_dec(x_69);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_87);
x_95 = l_Lean_Parser_ParserState_restore(x_86, x_84, x_85);
lean_dec(x_84);
x_96 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_Parser_categoryParser___elambda__1(x_96, x_97, x_1, x_95);
x_99 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_100 = l_Lean_Parser_ParserState_mkNode(x_98, x_99, x_80);
x_101 = 1;
x_102 = l_Lean_Parser_mergeOrElseErrors(x_100, x_72, x_69, x_101);
lean_dec(x_69);
return x_102;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_82);
lean_dec(x_1);
x_117 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_118 = l_Lean_Parser_ParserState_mkNode(x_81, x_117, x_80);
x_119 = 1;
x_120 = l_Lean_Parser_mergeOrElseErrors(x_118, x_72, x_69, x_119);
lean_dec(x_69);
return x_120;
}
}
block_129:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 3);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l_Lean_Parser_ParserState_restore(x_123, x_80, x_122);
x_126 = l_Lean_Parser_notFollowedByFn___closed__1;
x_127 = l_Lean_Parser_ParserState_mkError(x_125, x_126);
x_81 = x_127;
goto block_121;
}
else
{
lean_object* x_128; 
lean_dec(x_124);
x_128 = l_Lean_Parser_ParserState_restore(x_123, x_80, x_122);
x_81 = x_128;
goto block_121;
}
}
}
else
{
uint8_t x_143; lean_object* x_144; 
lean_dec(x_78);
lean_dec(x_1);
x_143 = 1;
x_144 = l_Lean_Parser_mergeOrElseErrors(x_77, x_72, x_69, x_143);
lean_dec(x_69);
return x_144;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_doExpr___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_doExpr___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_doExpr___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_doExpr___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doExpr___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doExpr___closed__5;
x_2 = l_Lean_Parser_Term_doExpr___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_doExpr___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_doExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_3 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_doExpr;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doExpr___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_have_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doExpr_formatter___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign_formatter___closed__1;
x_2 = l_Lean_Parser_Term_doExpr_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doExpr_formatter___closed__4;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doExpr_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doExpr_formatter___closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doExpr_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doAssign_parenthesizer___closed__1;
x_2 = l_Lean_Parser_Term_doExpr_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doExpr_parenthesizer___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doExpr_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doExpr_parenthesizer___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doExpr_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("do");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("do ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_do___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_do___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = l_Lean_Parser_maxPrec;
x_7 = l_Lean_Parser_checkPrecFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_1);
x_20 = l_Lean_Parser_tokenFn(x_1, x_7);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_Term_do___elambda__1___closed__6;
x_26 = lean_string_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_28 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_27, x_19);
x_11 = x_28;
goto block_18;
}
else
{
lean_dec(x_19);
x_11 = x_20;
goto block_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_29 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_29, x_19);
x_11 = x_30;
goto block_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_31 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_32 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_31, x_19);
x_11 = x_32;
goto block_18;
}
block_18:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Parser_Term_doSeq___elambda__1(x_1, x_11);
x_14 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_13, x_14, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_11, x_16, x_10);
return x_17;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_apply_2(x_4, x_1, x_2);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_nat_dec_eq(x_39, x_35);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_35);
x_41 = l_Lean_Parser_ParserState_restore(x_36, x_34, x_35);
lean_dec(x_34);
x_42 = l_Lean_Parser_maxPrec;
x_43 = l_Lean_Parser_checkPrecFn(x_42, x_1, x_41);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
lean_inc(x_1);
x_60 = l_Lean_Parser_tokenFn(x_1, x_43);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 2)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Parser_Term_do___elambda__1___closed__6;
x_66 = lean_string_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_68 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_67, x_59);
x_47 = x_68;
goto block_58;
}
else
{
lean_dec(x_59);
x_47 = x_60;
goto block_58;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
x_69 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_69, x_59);
x_47 = x_70;
goto block_58;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
x_71 = l_Lean_Parser_Term_do___elambda__1___closed__9;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_60, x_71, x_59);
x_47 = x_72;
goto block_58;
}
block_58:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_49 = l_Lean_Parser_Term_doSeq___elambda__1(x_1, x_47);
x_50 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_46);
x_52 = 1;
x_53 = l_Lean_Parser_mergeOrElseErrors(x_51, x_38, x_35, x_52);
lean_dec(x_35);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_47, x_54, x_46);
x_56 = 1;
x_57 = l_Lean_Parser_mergeOrElseErrors(x_55, x_38, x_35, x_56);
lean_dec(x_35);
return x_57;
}
}
}
else
{
uint8_t x_73; lean_object* x_74; 
lean_dec(x_44);
lean_dec(x_1);
x_73 = 1;
x_74 = l_Lean_Parser_mergeOrElseErrors(x_43, x_38, x_35, x_73);
lean_dec(x_35);
return x_74;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__6;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeq;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_do___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_do___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Term_do___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_do___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_do___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_do___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_do___closed__5;
x_2 = l_Lean_Parser_Term_do___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_do___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_do(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean___kind_term____x40_Lean_Util_Trace___hyg_3____closed__15;
x_3 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_do;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Lean_Parser_doElemParser_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_doElemParser_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_formatter___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_doElemParser_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_doElemParser_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_formatter___rarg), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2;
x_2 = l_Lean_Parser_Tactic_indentedNonEmptySeq_formatter___lambda__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_sepBy1_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3;
x_2 = l_Lean_Parser_Term_emptyC_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_emptyC_formatter___closed__3;
x_2 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2;
x_8 = l_Lean_Parser_Tactic_indentedNonEmptySeq_formatter___lambda__1___closed__4;
x_9 = l_Lean_PrettyPrinter_Formatter_sepBy_formatter(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_Term_doSeqIndent_formatter___closed__1;
x_7 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_Term_doSeqIndent_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_formatter), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_formatter), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Term_doSeq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doSeq_formatter___closed__1;
x_7 = l_Lean_Parser_Term_doSeq_formatter___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_do_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_do_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_do_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_do_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_do_formatter___closed__2;
x_2 = l_Lean_Parser_Term_do_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_Term_do_formatter___closed__4;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_do_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_do_formatter___closed__1;
x_7 = l_Lean_Parser_Term_do_formatter___closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_do_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_do_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_doElemParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3;
x_2 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2;
x_8 = l_Lean_Parser_Tactic_indentedNonEmptySeq_parenthesizer___lambda__1___closed__4;
x_9 = l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1;
x_7 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_Term_doSeqIndent_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_doSeq_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Term_doSeq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_doSeq_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_doSeq_parenthesizer___closed__2;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Term_do_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__3;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___rarg___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_do_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_do_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3;
x_2 = l_Lean_Parser_Term_do_parenthesizer___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_do_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_Term_do_parenthesizer___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_do_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Term_do_parenthesizer___closed__1;
x_7 = l_Lean_Parser_Term_do_parenthesizer___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_do_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Parser_Term_do_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Do(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinDoElemParserAttr___closed__1);
l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinDoElemParserAttr___closed__2);
l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinDoElemParserAttr___closed__3);
l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinDoElemParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinDoElemParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regDoElemParserAttribute___closed__1 = _init_l_Lean_Parser_regDoElemParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regDoElemParserAttribute___closed__1);
l_Lean_Parser_regDoElemParserAttribute___closed__2 = _init_l_Lean_Parser_regDoElemParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regDoElemParserAttribute___closed__2);
res = l_Lean_Parser_regDoElemParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__1 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__1);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__2 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__2);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__3 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__3);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__4 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__4);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__5 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__5);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__6 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__6);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__7 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__7);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__8 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__8);
l_Lean_Parser_Term_leftArrow___elambda__1___closed__9 = _init_l_Lean_Parser_Term_leftArrow___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___elambda__1___closed__9);
l_Lean_Parser_Term_leftArrow___closed__1 = _init_l_Lean_Parser_Term_leftArrow___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___closed__1);
l_Lean_Parser_Term_leftArrow___closed__2 = _init_l_Lean_Parser_Term_leftArrow___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___closed__2);
l_Lean_Parser_Term_leftArrow___closed__3 = _init_l_Lean_Parser_Term_leftArrow___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow___closed__3);
l_Lean_Parser_Term_leftArrow = _init_l_Lean_Parser_Term_leftArrow();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow);
l_Lean_Parser_Term_liftMethod___elambda__1___closed__1 = _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___elambda__1___closed__1);
l_Lean_Parser_Term_liftMethod___elambda__1___closed__2 = _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___elambda__1___closed__2);
l_Lean_Parser_Term_liftMethod___elambda__1___closed__3 = _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___elambda__1___closed__3);
l_Lean_Parser_Term_liftMethod___elambda__1___closed__4 = _init_l_Lean_Parser_Term_liftMethod___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___elambda__1___closed__4);
l_Lean_Parser_Term_liftMethod___closed__1 = _init_l_Lean_Parser_Term_liftMethod___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__1);
l_Lean_Parser_Term_liftMethod___closed__2 = _init_l_Lean_Parser_Term_liftMethod___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__2);
l_Lean_Parser_Term_liftMethod___closed__3 = _init_l_Lean_Parser_Term_liftMethod___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__3);
l_Lean_Parser_Term_liftMethod___closed__4 = _init_l_Lean_Parser_Term_liftMethod___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__4);
l_Lean_Parser_Term_liftMethod___closed__5 = _init_l_Lean_Parser_Term_liftMethod___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__5);
l_Lean_Parser_Term_liftMethod___closed__6 = _init_l_Lean_Parser_Term_liftMethod___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod___closed__6);
l_Lean_Parser_Term_liftMethod = _init_l_Lean_Parser_Term_liftMethod();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod);
res = l___regBuiltinParser_Lean_Parser_Term_liftMethod(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_liftMethod_formatter___closed__1 = _init_l_Lean_Parser_Term_liftMethod_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_formatter___closed__1);
l_Lean_Parser_Term_liftMethod_formatter___closed__2 = _init_l_Lean_Parser_Term_liftMethod_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_formatter___closed__2);
l_Lean_Parser_Term_liftMethod_formatter___closed__3 = _init_l_Lean_Parser_Term_liftMethod_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_formatter___closed__3);
l_Lean_Parser_Term_liftMethod_formatter___closed__4 = _init_l_Lean_Parser_Term_liftMethod_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_formatter___closed__4);
l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_liftMethod_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_liftMethod_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_parenthesizer___closed__1);
l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_parenthesizer___closed__2);
l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_parenthesizer___closed__3);
l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod_parenthesizer___closed__4);
l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1 = _init_l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_doSeqIndent___elambda__1___spec__2___closed__1);
l_Lean_Parser_Term_doSeqIndent___closed__1 = _init_l_Lean_Parser_Term_doSeqIndent___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent___closed__1);
l_Lean_Parser_Term_doSeqIndent___closed__2 = _init_l_Lean_Parser_Term_doSeqIndent___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent___closed__2);
l_Lean_Parser_Term_doSeqIndent___closed__3 = _init_l_Lean_Parser_Term_doSeqIndent___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent___closed__3);
l_Lean_Parser_Term_doSeqIndent___closed__4 = _init_l_Lean_Parser_Term_doSeqIndent___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent___closed__4);
l_Lean_Parser_Term_doSeqIndent = _init_l_Lean_Parser_Term_doSeqIndent();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent);
l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__1);
l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__2);
l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__3);
l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___elambda__1___closed__4);
l_Lean_Parser_Term_doSeqBracketed___closed__1 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__1);
l_Lean_Parser_Term_doSeqBracketed___closed__2 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__2);
l_Lean_Parser_Term_doSeqBracketed___closed__3 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__3);
l_Lean_Parser_Term_doSeqBracketed___closed__4 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__4);
l_Lean_Parser_Term_doSeqBracketed___closed__5 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__5);
l_Lean_Parser_Term_doSeqBracketed___closed__6 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__6);
l_Lean_Parser_Term_doSeqBracketed___closed__7 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__7);
l_Lean_Parser_Term_doSeqBracketed___closed__8 = _init_l_Lean_Parser_Term_doSeqBracketed___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed___closed__8);
l_Lean_Parser_Term_doSeqBracketed = _init_l_Lean_Parser_Term_doSeqBracketed();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed);
l_Lean_Parser_Term_doSeq___closed__1 = _init_l_Lean_Parser_Term_doSeq___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeq___closed__1);
l_Lean_Parser_Term_doSeq___closed__2 = _init_l_Lean_Parser_Term_doSeq___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeq___closed__2);
l_Lean_Parser_Term_doSeq___closed__3 = _init_l_Lean_Parser_Term_doSeq___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeq___closed__3);
l_Lean_Parser_Term_doSeq = _init_l_Lean_Parser_Term_doSeq();
lean_mark_persistent(l_Lean_Parser_Term_doSeq);
l_Lean_Parser_Term_doLet___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doLet___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doLet___elambda__1___closed__1);
l_Lean_Parser_Term_doLet___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doLet___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doLet___elambda__1___closed__2);
l_Lean_Parser_Term_doLet___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doLet___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doLet___elambda__1___closed__3);
l_Lean_Parser_Term_doLet___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doLet___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doLet___elambda__1___closed__4);
l_Lean_Parser_Term_doLet___closed__1 = _init_l_Lean_Parser_Term_doLet___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__1);
l_Lean_Parser_Term_doLet___closed__2 = _init_l_Lean_Parser_Term_doLet___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__2);
l_Lean_Parser_Term_doLet___closed__3 = _init_l_Lean_Parser_Term_doLet___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__3);
l_Lean_Parser_Term_doLet___closed__4 = _init_l_Lean_Parser_Term_doLet___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__4);
l_Lean_Parser_Term_doLet___closed__5 = _init_l_Lean_Parser_Term_doLet___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__5);
l_Lean_Parser_Term_doLet___closed__6 = _init_l_Lean_Parser_Term_doLet___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doLet___closed__6);
l_Lean_Parser_Term_doLet = _init_l_Lean_Parser_Term_doLet();
lean_mark_persistent(l_Lean_Parser_Term_doLet);
res = l___regBuiltinParser_Lean_Parser_Term_doLet(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doLet_formatter___closed__1 = _init_l_Lean_Parser_Term_doLet_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doLet_formatter___closed__1);
l_Lean_Parser_Term_doLet_formatter___closed__2 = _init_l_Lean_Parser_Term_doLet_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doLet_formatter___closed__2);
l_Lean_Parser_Term_doLet_formatter___closed__3 = _init_l_Lean_Parser_Term_doLet_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doLet_formatter___closed__3);
l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doLet_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doLet_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doLet_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doLet_parenthesizer___closed__1);
l_Lean_Parser_Term_doLet_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doLet_parenthesizer___closed__2);
l_Lean_Parser_Term_doLet_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doLet_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doLet_parenthesizer___closed__3);
l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doId___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doId___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doId___elambda__1___closed__1);
l_Lean_Parser_Term_doId___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doId___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doId___elambda__1___closed__2);
l_Lean_Parser_Term_doId___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doId___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doId___elambda__1___closed__3);
l_Lean_Parser_Term_doId___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doId___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doId___elambda__1___closed__4);
l_Lean_Parser_Term_doId___closed__1 = _init_l_Lean_Parser_Term_doId___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__1);
l_Lean_Parser_Term_doId___closed__2 = _init_l_Lean_Parser_Term_doId___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__2);
l_Lean_Parser_Term_doId___closed__3 = _init_l_Lean_Parser_Term_doId___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__3);
l_Lean_Parser_Term_doId___closed__4 = _init_l_Lean_Parser_Term_doId___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__4);
l_Lean_Parser_Term_doId___closed__5 = _init_l_Lean_Parser_Term_doId___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__5);
l_Lean_Parser_Term_doId___closed__6 = _init_l_Lean_Parser_Term_doId___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__6);
l_Lean_Parser_Term_doId___closed__7 = _init_l_Lean_Parser_Term_doId___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__7);
l_Lean_Parser_Term_doId___closed__8 = _init_l_Lean_Parser_Term_doId___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_doId___closed__8);
l_Lean_Parser_Term_doId = _init_l_Lean_Parser_Term_doId();
lean_mark_persistent(l_Lean_Parser_Term_doId);
l_Lean_Parser_Term_doPat___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__1);
l_Lean_Parser_Term_doPat___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__2);
l_Lean_Parser_Term_doPat___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__3);
l_Lean_Parser_Term_doPat___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__4);
l_Lean_Parser_Term_doPat___elambda__1___closed__5 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__5);
l_Lean_Parser_Term_doPat___elambda__1___closed__6 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__6);
l_Lean_Parser_Term_doPat___elambda__1___closed__7 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__7);
l_Lean_Parser_Term_doPat___elambda__1___closed__8 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__8);
l_Lean_Parser_Term_doPat___elambda__1___closed__9 = _init_l_Lean_Parser_Term_doPat___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_doPat___elambda__1___closed__9);
l_Lean_Parser_Term_doPat___closed__1 = _init_l_Lean_Parser_Term_doPat___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__1);
l_Lean_Parser_Term_doPat___closed__2 = _init_l_Lean_Parser_Term_doPat___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__2);
l_Lean_Parser_Term_doPat___closed__3 = _init_l_Lean_Parser_Term_doPat___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__3);
l_Lean_Parser_Term_doPat___closed__4 = _init_l_Lean_Parser_Term_doPat___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__4);
l_Lean_Parser_Term_doPat___closed__5 = _init_l_Lean_Parser_Term_doPat___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__5);
l_Lean_Parser_Term_doPat___closed__6 = _init_l_Lean_Parser_Term_doPat___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__6);
l_Lean_Parser_Term_doPat___closed__7 = _init_l_Lean_Parser_Term_doPat___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__7);
l_Lean_Parser_Term_doPat___closed__8 = _init_l_Lean_Parser_Term_doPat___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__8);
l_Lean_Parser_Term_doPat___closed__9 = _init_l_Lean_Parser_Term_doPat___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__9);
l_Lean_Parser_Term_doPat___closed__10 = _init_l_Lean_Parser_Term_doPat___closed__10();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__10);
l_Lean_Parser_Term_doPat___closed__11 = _init_l_Lean_Parser_Term_doPat___closed__11();
lean_mark_persistent(l_Lean_Parser_Term_doPat___closed__11);
l_Lean_Parser_Term_doPat = _init_l_Lean_Parser_Term_doPat();
lean_mark_persistent(l_Lean_Parser_Term_doPat);
l_Lean_Parser_Term_doAssign___closed__1 = _init_l_Lean_Parser_Term_doAssign___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doAssign___closed__1);
l_Lean_Parser_Term_doAssign___closed__2 = _init_l_Lean_Parser_Term_doAssign___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doAssign___closed__2);
l_Lean_Parser_Term_doAssign___closed__3 = _init_l_Lean_Parser_Term_doAssign___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doAssign___closed__3);
l_Lean_Parser_Term_doAssign___closed__4 = _init_l_Lean_Parser_Term_doAssign___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doAssign___closed__4);
l_Lean_Parser_Term_doAssign = _init_l_Lean_Parser_Term_doAssign();
lean_mark_persistent(l_Lean_Parser_Term_doAssign);
l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__1);
l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2 = _init_l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Term_doAssign___closed__2);
res = l___regBuiltinParser_Lean_Parser_Term_doAssign(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doId_formatter___closed__1 = _init_l_Lean_Parser_Term_doId_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__1);
l_Lean_Parser_Term_doId_formatter___closed__2 = _init_l_Lean_Parser_Term_doId_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__2);
l_Lean_Parser_Term_doId_formatter___closed__3 = _init_l_Lean_Parser_Term_doId_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__3);
l_Lean_Parser_Term_doId_formatter___closed__4 = _init_l_Lean_Parser_Term_doId_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__4);
l_Lean_Parser_Term_doId_formatter___closed__5 = _init_l_Lean_Parser_Term_doId_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__5);
l_Lean_Parser_Term_doId_formatter___closed__6 = _init_l_Lean_Parser_Term_doId_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doId_formatter___closed__6);
l_Lean_Parser_Term_doPat_formatter___closed__1 = _init_l_Lean_Parser_Term_doPat_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__1);
l_Lean_Parser_Term_doPat_formatter___closed__2 = _init_l_Lean_Parser_Term_doPat_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__2);
l_Lean_Parser_Term_doPat_formatter___closed__3 = _init_l_Lean_Parser_Term_doPat_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__3);
l_Lean_Parser_Term_doPat_formatter___closed__4 = _init_l_Lean_Parser_Term_doPat_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__4);
l_Lean_Parser_Term_doPat_formatter___closed__5 = _init_l_Lean_Parser_Term_doPat_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__5);
l_Lean_Parser_Term_doPat_formatter___closed__6 = _init_l_Lean_Parser_Term_doPat_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__6);
l_Lean_Parser_Term_doPat_formatter___closed__7 = _init_l_Lean_Parser_Term_doPat_formatter___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__7);
l_Lean_Parser_Term_doPat_formatter___closed__8 = _init_l_Lean_Parser_Term_doPat_formatter___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__8);
l_Lean_Parser_Term_doPat_formatter___closed__9 = _init_l_Lean_Parser_Term_doPat_formatter___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_doPat_formatter___closed__9);
l_Lean_Parser_Term_doAssign_formatter___closed__1 = _init_l_Lean_Parser_Term_doAssign_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_formatter___closed__1);
l_Lean_Parser_Term_doAssign_formatter___closed__2 = _init_l_Lean_Parser_Term_doAssign_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_formatter___closed__2);
l_Lean_Parser_Term_doAssign_formatter___closed__3 = _init_l_Lean_Parser_Term_doAssign_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_formatter___closed__3);
l_Lean_Parser_Term_doAssign_formatter___closed__4 = _init_l_Lean_Parser_Term_doAssign_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_formatter___closed__4);
l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doAssign_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doAssign_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doId_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__1);
l_Lean_Parser_Term_doId_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__2);
l_Lean_Parser_Term_doId_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__3);
l_Lean_Parser_Term_doId_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__4);
l_Lean_Parser_Term_doId_parenthesizer___closed__5 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__5);
l_Lean_Parser_Term_doId_parenthesizer___closed__6 = _init_l_Lean_Parser_Term_doId_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doId_parenthesizer___closed__6);
l_Lean_Parser_Term_doPat_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__1);
l_Lean_Parser_Term_doPat_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__2);
l_Lean_Parser_Term_doPat_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__3);
l_Lean_Parser_Term_doPat_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__4);
l_Lean_Parser_Term_doPat_parenthesizer___closed__5 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__5);
l_Lean_Parser_Term_doPat_parenthesizer___closed__6 = _init_l_Lean_Parser_Term_doPat_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doPat_parenthesizer___closed__6);
l_Lean_Parser_Term_doAssign_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_parenthesizer___closed__1);
l_Lean_Parser_Term_doAssign_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_parenthesizer___closed__2);
l_Lean_Parser_Term_doAssign_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_parenthesizer___closed__3);
l_Lean_Parser_Term_doAssign_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_doAssign_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doAssign_parenthesizer___closed__4);
l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doAssign_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doHave___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doHave___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doHave___elambda__1___closed__1);
l_Lean_Parser_Term_doHave___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doHave___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doHave___elambda__1___closed__2);
l_Lean_Parser_Term_doHave___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doHave___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doHave___elambda__1___closed__3);
l_Lean_Parser_Term_doHave___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doHave___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doHave___elambda__1___closed__4);
l_Lean_Parser_Term_doHave___closed__1 = _init_l_Lean_Parser_Term_doHave___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__1);
l_Lean_Parser_Term_doHave___closed__2 = _init_l_Lean_Parser_Term_doHave___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__2);
l_Lean_Parser_Term_doHave___closed__3 = _init_l_Lean_Parser_Term_doHave___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__3);
l_Lean_Parser_Term_doHave___closed__4 = _init_l_Lean_Parser_Term_doHave___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__4);
l_Lean_Parser_Term_doHave___closed__5 = _init_l_Lean_Parser_Term_doHave___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__5);
l_Lean_Parser_Term_doHave___closed__6 = _init_l_Lean_Parser_Term_doHave___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doHave___closed__6);
l_Lean_Parser_Term_doHave = _init_l_Lean_Parser_Term_doHave();
lean_mark_persistent(l_Lean_Parser_Term_doHave);
res = l___regBuiltinParser_Lean_Parser_Term_doHave(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doHave_formatter___closed__1 = _init_l_Lean_Parser_Term_doHave_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doHave_formatter___closed__1);
l_Lean_Parser_Term_doHave_formatter___closed__2 = _init_l_Lean_Parser_Term_doHave_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doHave_formatter___closed__2);
l_Lean_Parser_Term_doHave_formatter___closed__3 = _init_l_Lean_Parser_Term_doHave_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doHave_formatter___closed__3);
l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doHave_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doHave_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doHave_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doHave_parenthesizer___closed__1);
l_Lean_Parser_Term_doHave_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doHave_parenthesizer___closed__2);
l_Lean_Parser_Term_doHave_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doHave_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doHave_parenthesizer___closed__3);
l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doExpr___elambda__1___closed__1 = _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___elambda__1___closed__1);
l_Lean_Parser_Term_doExpr___elambda__1___closed__2 = _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___elambda__1___closed__2);
l_Lean_Parser_Term_doExpr___elambda__1___closed__3 = _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___elambda__1___closed__3);
l_Lean_Parser_Term_doExpr___elambda__1___closed__4 = _init_l_Lean_Parser_Term_doExpr___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___elambda__1___closed__4);
l_Lean_Parser_Term_doExpr___closed__1 = _init_l_Lean_Parser_Term_doExpr___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__1);
l_Lean_Parser_Term_doExpr___closed__2 = _init_l_Lean_Parser_Term_doExpr___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__2);
l_Lean_Parser_Term_doExpr___closed__3 = _init_l_Lean_Parser_Term_doExpr___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__3);
l_Lean_Parser_Term_doExpr___closed__4 = _init_l_Lean_Parser_Term_doExpr___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__4);
l_Lean_Parser_Term_doExpr___closed__5 = _init_l_Lean_Parser_Term_doExpr___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__5);
l_Lean_Parser_Term_doExpr___closed__6 = _init_l_Lean_Parser_Term_doExpr___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__6);
l_Lean_Parser_Term_doExpr___closed__7 = _init_l_Lean_Parser_Term_doExpr___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_doExpr___closed__7);
l_Lean_Parser_Term_doExpr = _init_l_Lean_Parser_Term_doExpr();
lean_mark_persistent(l_Lean_Parser_Term_doExpr);
res = l___regBuiltinParser_Lean_Parser_Term_doExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doExpr_formatter___closed__1 = _init_l_Lean_Parser_Term_doExpr_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_formatter___closed__1);
l_Lean_Parser_Term_doExpr_formatter___closed__2 = _init_l_Lean_Parser_Term_doExpr_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_formatter___closed__2);
l_Lean_Parser_Term_doExpr_formatter___closed__3 = _init_l_Lean_Parser_Term_doExpr_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_formatter___closed__3);
l_Lean_Parser_Term_doExpr_formatter___closed__4 = _init_l_Lean_Parser_Term_doExpr_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_formatter___closed__4);
l_Lean_Parser_Term_doExpr_formatter___closed__5 = _init_l_Lean_Parser_Term_doExpr_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_formatter___closed__5);
l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doExpr_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doExpr_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doExpr_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_parenthesizer___closed__1);
l_Lean_Parser_Term_doExpr_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_parenthesizer___closed__2);
l_Lean_Parser_Term_doExpr_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_parenthesizer___closed__3);
l_Lean_Parser_Term_doExpr_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_doExpr_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doExpr_parenthesizer___closed__4);
l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_do___elambda__1___closed__1 = _init_l_Lean_Parser_Term_do___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__1);
l_Lean_Parser_Term_do___elambda__1___closed__2 = _init_l_Lean_Parser_Term_do___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__2);
l_Lean_Parser_Term_do___elambda__1___closed__3 = _init_l_Lean_Parser_Term_do___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__3);
l_Lean_Parser_Term_do___elambda__1___closed__4 = _init_l_Lean_Parser_Term_do___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__4);
l_Lean_Parser_Term_do___elambda__1___closed__5 = _init_l_Lean_Parser_Term_do___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__5);
l_Lean_Parser_Term_do___elambda__1___closed__6 = _init_l_Lean_Parser_Term_do___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__6);
l_Lean_Parser_Term_do___elambda__1___closed__7 = _init_l_Lean_Parser_Term_do___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__7);
l_Lean_Parser_Term_do___elambda__1___closed__8 = _init_l_Lean_Parser_Term_do___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__8);
l_Lean_Parser_Term_do___elambda__1___closed__9 = _init_l_Lean_Parser_Term_do___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_do___elambda__1___closed__9);
l_Lean_Parser_Term_do___closed__1 = _init_l_Lean_Parser_Term_do___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__1);
l_Lean_Parser_Term_do___closed__2 = _init_l_Lean_Parser_Term_do___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__2);
l_Lean_Parser_Term_do___closed__3 = _init_l_Lean_Parser_Term_do___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__3);
l_Lean_Parser_Term_do___closed__4 = _init_l_Lean_Parser_Term_do___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__4);
l_Lean_Parser_Term_do___closed__5 = _init_l_Lean_Parser_Term_do___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__5);
l_Lean_Parser_Term_do___closed__6 = _init_l_Lean_Parser_Term_do___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__6);
l_Lean_Parser_Term_do___closed__7 = _init_l_Lean_Parser_Term_do___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_do___closed__7);
l_Lean_Parser_Term_do = _init_l_Lean_Parser_Term_do();
lean_mark_persistent(l_Lean_Parser_Term_do);
res = l___regBuiltinParser_Lean_Parser_Term_do(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__1);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__2);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__3);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__4);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__5);
l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6 = _init_l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_formatter___closed__6);
l_Lean_Parser_Term_doSeqIndent_formatter___closed__1 = _init_l_Lean_Parser_Term_doSeqIndent_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent_formatter___closed__1);
l_Lean_Parser_Term_doSeq_formatter___closed__1 = _init_l_Lean_Parser_Term_doSeq_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeq_formatter___closed__1);
l_Lean_Parser_Term_doSeq_formatter___closed__2 = _init_l_Lean_Parser_Term_doSeq_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeq_formatter___closed__2);
l_Lean_Parser_Term_do_formatter___closed__1 = _init_l_Lean_Parser_Term_do_formatter___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_do_formatter___closed__1);
l_Lean_Parser_Term_do_formatter___closed__2 = _init_l_Lean_Parser_Term_do_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_do_formatter___closed__2);
l_Lean_Parser_Term_do_formatter___closed__3 = _init_l_Lean_Parser_Term_do_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_do_formatter___closed__3);
l_Lean_Parser_Term_do_formatter___closed__4 = _init_l_Lean_Parser_Term_do_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_do_formatter___closed__4);
l_Lean_Parser_Term_do_formatter___closed__5 = _init_l_Lean_Parser_Term_do_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_do_formatter___closed__5);
l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_do_formatter___closed__1);
res = l___regBuiltin_Lean_Parser_Term_do_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__1);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__2);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__3);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__4);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__5);
l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6 = _init_l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___closed__6);
l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent_parenthesizer___closed__1);
l_Lean_Parser_Term_doSeq_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_doSeq_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_doSeq_parenthesizer___closed__1);
l_Lean_Parser_Term_doSeq_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_doSeq_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_doSeq_parenthesizer___closed__2);
l_Lean_Parser_Term_do_parenthesizer___closed__1 = _init_l_Lean_Parser_Term_do_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_do_parenthesizer___closed__1);
l_Lean_Parser_Term_do_parenthesizer___closed__2 = _init_l_Lean_Parser_Term_do_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_do_parenthesizer___closed__2);
l_Lean_Parser_Term_do_parenthesizer___closed__3 = _init_l_Lean_Parser_Term_do_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_do_parenthesizer___closed__3);
l_Lean_Parser_Term_do_parenthesizer___closed__4 = _init_l_Lean_Parser_Term_do_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_do_parenthesizer___closed__4);
l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_Term_do_parenthesizer___closed__1);
res = l___regBuiltin_Lean_Parser_Term_do_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
