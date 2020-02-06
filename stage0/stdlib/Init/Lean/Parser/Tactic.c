// Lean compiler output
// Module: Init.Lean.Parser.Tactic
// Imports: Init.Lean.Parser.Term
#include "runtime/lean.h"
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
lean_object* l_Lean_Parser_Tactic_orelse___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intro(lean_object*);
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___closed__6;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4;
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__6;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_apply___closed__2;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__5;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_orelse___closed__1;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_underscore___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_seq;
lean_object* l_Lean_Parser_Tactic_skip___closed__3;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_have___closed__3;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly;
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_Tactic_underscore___closed__1;
extern lean_object* l_Lean_Parser_Term_subtype___closed__1;
lean_object* l_Lean_Parser_Tactic_skip___closed__2;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__4;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__3;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__7;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__1;
lean_object* l_Lean_Parser_Tactic_underscore;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_paren___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_refine___closed__5;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___closed__1;
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__3;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_termIdToAntiquot___closed__3;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___closed__3;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq;
lean_object* l_Lean_Parser_Tactic_skip___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___closed__5;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___closed__5;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__6;
lean_object* l_Lean_Parser_tacticParser(lean_object*);
lean_object* l_Lean_Parser_Tactic_case___closed__4;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__6;
lean_object* l_Lean_Parser_Tactic_assumption;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___closed__5;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__5;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case;
lean_object* l_Lean_Parser_Tactic_traceState___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals;
lean_object* l_Lean_Parser_Tactic_refine___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_case(lean_object*);
lean_object* l_Lean_Parser_Tactic_seq___closed__5;
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__5;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_seq___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___closed__2;
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__2;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_intros___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__2;
lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___closed__5;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__13;
extern lean_object* l_Lean_Parser_termParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__6;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___closed__3;
lean_object* l_Lean_Parser_Tactic_paren___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___closed__2;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_ident_x27;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_exact___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Parser_Tactic_paren___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__5;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock;
extern lean_object* l_Lean_Parser_Term_explicitUniv___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_refine___closed__6;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___closed__2;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply;
lean_object* l_Lean_Parser_Tactic_assumption___closed__5;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_paren___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_paren___closed__2;
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1;
extern lean_object* l_Lean_Parser_Term_seq___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_case___closed__5;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__6;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2;
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__6;
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_underscoreFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_refine___closed__1;
lean_object* l_Lean_Parser_Tactic_paren___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_refine___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_exact(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_case___closed__3;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_allGoals(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__4;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_case___closed__1;
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___closed__5;
lean_object* l_Lean_Parser_Tactic_paren___closed__6;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4;
lean_object* l_Lean_Parser_Tactic_assumption___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__7;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__8;
lean_object* l_Lean_Parser_Term_tacticBlock;
lean_object* l_Lean_Parser_Tactic_case___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__4;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__6;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__3;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__7;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_paren(lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__2;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__1;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___closed__2;
lean_object* l_Lean_Parser_Tactic_intro___closed__2;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__5;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__1;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__5;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__4;
lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___closed__3;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_orelse___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__5;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_skip(lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_skip;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___closed__1;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_traceState(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__5;
lean_object* l_Lean_Parser_Tactic_paren;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro;
lean_object* l_Lean_Parser_Tactic_refine;
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__3;
extern lean_object* l_Lean_ppGoal___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_refine(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_skip___closed__4;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__4;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_seq___closed__4;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTacticParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = 1;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_regTacticParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regTacticParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regTacticParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regTacticParserAttribute___closed__2;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_tacticParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_underscoreFn___closed__1;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_underscoreFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_underscoreFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkHole___closed__3;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parser_Tactic_underscoreFn___closed__3;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_19, x_3);
x_6 = x_20;
goto block_13;
}
else
{
lean_dec(x_3);
x_6 = x_4;
goto block_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = l_Lean_Parser_Tactic_underscoreFn___closed__3;
x_22 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_21, x_3);
x_6 = x_22;
goto block_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parser_Tactic_underscoreFn___closed__3;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_23, x_3);
x_6 = x_24;
goto block_13;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_7);
lean_dec(x_7);
x_9 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_10 = l_Lean_Parser_Tactic_underscoreFn___closed__4;
x_11 = l_Lean_mkIdentFrom(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Parser_ParserState_pushSyntax(x_9, x_11);
return x_12;
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_underscoreFn), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identNoAntiquot___closed__1;
x_2 = l_Lean_Parser_Tactic_underscore___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscore() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_underscore___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_Parser_ident___elambda__1(x_1, x_2);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_11 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_12 = l_Lean_Parser_Tactic_underscoreFn(x_1, x_11);
x_13 = l_Lean_Parser_mergeOrElseErrors(x_12, x_8, x_5);
lean_dec(x_5);
return x_13;
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_ident_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_identNoAntiquot___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_ident_x27___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_ident_x27___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_ident_x27___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_ident_x27___closed__1;
x_2 = l_Lean_Parser_Tactic_ident_x27___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_ident_x27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_ident_x27___closed__3;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_12 = l_Lean_Parser_categoryParser___elambda__1(x_10, x_11, x_5, x_6);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_5);
x_31 = l_Lean_Parser_tokenFn(x_5, x_12);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 2)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Parser_Term_have___elambda__1___closed__7;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_16);
x_39 = l_Lean_Parser_ParserState_mkErrorsAt(x_31, x_38, x_16);
x_17 = x_39;
goto block_30;
}
else
{
x_17 = x_31;
goto block_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
x_40 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_16);
x_41 = l_Lean_Parser_ParserState_mkErrorsAt(x_31, x_40, x_16);
x_17 = x_41;
goto block_30;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
x_42 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_16);
x_43 = l_Lean_Parser_ParserState_mkErrorsAt(x_31, x_42, x_16);
x_17 = x_43;
goto block_30;
}
block_30:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
{
uint8_t _tmp_3 = x_1;
lean_object* _tmp_5 = x_17;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_5);
x_20 = l_Lean_Parser_ParserState_restore(x_17, x_15, x_16);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_nat_sub(x_22, x_2);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_20, x_26, x_2);
return x_27;
}
else
{
if (x_3 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_20, x_28, x_2);
return x_29;
}
else
{
lean_dec(x_2);
return x_20;
}
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_44);
x_46 = l_Lean_nullKind;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = l_Lean_Parser_ParserState_restore(x_12, x_8, x_9);
lean_dec(x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_array_get_size(x_49);
lean_dec(x_49);
x_51 = lean_nat_sub(x_50, x_2);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_nullKind;
x_55 = l_Lean_Parser_ParserState_mkNode(x_48, x_54, x_2);
return x_55;
}
else
{
if (x_3 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_nullKind;
x_57 = l_Lean_Parser_ParserState_mkNode(x_48, x_56, x_2);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_2);
x_58 = l_Lean_Parser_ParserState_popSyntax(x_48);
return x_58;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(x_1, x_6, x_2, x_7, x_3, x_4);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_seq___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_seq___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = 0;
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_have___closed__3;
x_4 = l_Lean_Parser_sepBy1Info(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_2 = l_Lean_Parser_Tactic_seq___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___closed__3;
x_2 = l_Lean_Parser_Tactic_seq___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_seq___closed__5;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = 0;
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nonEmptySeq___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___closed__3;
x_2 = l_Lean_Parser_Tactic_nonEmptySeq___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_nonEmptySeq___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intro");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intro ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_3 = l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_140 = lean_ctor_get(x_2, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
x_143 = lean_nat_dec_eq(x_141, x_142);
lean_dec(x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_140);
lean_inc(x_1);
x_144 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_144;
goto block_139;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_140, 2);
lean_inc(x_145);
lean_dec(x_140);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_2);
lean_ctor_set(x_147, 1, x_146);
x_5 = x_147;
goto block_139;
}
block_139:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_12);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_17, x_19, x_15);
x_21 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_9);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_18);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
x_24 = lean_nat_dec_eq(x_23, x_16);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_17, x_25, x_15);
x_27 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Parser_ParserState_restore(x_17, x_15, x_16);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_15);
x_32 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_9);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
lean_dec(x_1);
x_34 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_12, x_34, x_9);
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
if (lean_obj_tag(x_36) == 2)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_4);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_array_get_size(x_41);
lean_dec(x_41);
x_43 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_44 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_45 = l_Lean_Parser_nonReservedSymbolFnAux(x_43, x_44, x_1, x_37);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
x_50 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_45);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_50, x_52, x_48);
x_54 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_42);
return x_55;
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_51);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
x_57 = lean_nat_dec_eq(x_56, x_49);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
x_58 = l_Lean_nullKind;
x_59 = l_Lean_Parser_ParserState_mkNode(x_50, x_58, x_48);
x_60 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_59, x_60, x_42);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = l_Lean_Parser_ParserState_restore(x_50, x_48, x_49);
x_63 = l_Lean_nullKind;
x_64 = l_Lean_Parser_ParserState_mkNode(x_62, x_63, x_48);
x_65 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_66 = l_Lean_Parser_ParserState_mkNode(x_64, x_65, x_42);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_46);
lean_dec(x_1);
x_67 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_68 = l_Lean_Parser_ParserState_mkNode(x_45, x_67, x_42);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_37, 0);
lean_inc(x_69);
x_70 = lean_array_get_size(x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_37, 1);
lean_inc(x_71);
lean_inc(x_1);
x_72 = lean_apply_2(x_4, x_1, x_37);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_nat_dec_eq(x_75, x_71);
lean_dec(x_75);
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_71);
x_77 = l_Lean_Parser_ParserState_restore(x_72, x_70, x_71);
lean_dec(x_70);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_array_get_size(x_78);
lean_dec(x_78);
x_80 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_81 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_82 = l_Lean_Parser_nonReservedSymbolFnAux(x_80, x_81, x_1, x_77);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_array_get_size(x_84);
lean_dec(x_84);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
x_87 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_82);
x_88 = lean_ctor_get(x_87, 3);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
x_89 = l_Lean_nullKind;
x_90 = l_Lean_Parser_ParserState_mkNode(x_87, x_89, x_85);
x_91 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_79);
x_93 = l_Lean_Parser_mergeOrElseErrors(x_92, x_74, x_71);
lean_dec(x_71);
return x_93;
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_88);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
x_95 = lean_nat_dec_eq(x_94, x_86);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_86);
x_96 = l_Lean_nullKind;
x_97 = l_Lean_Parser_ParserState_mkNode(x_87, x_96, x_85);
x_98 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_99 = l_Lean_Parser_ParserState_mkNode(x_97, x_98, x_79);
x_100 = l_Lean_Parser_mergeOrElseErrors(x_99, x_74, x_71);
lean_dec(x_71);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = l_Lean_Parser_ParserState_restore(x_87, x_85, x_86);
x_102 = l_Lean_nullKind;
x_103 = l_Lean_Parser_ParserState_mkNode(x_101, x_102, x_85);
x_104 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_105 = l_Lean_Parser_ParserState_mkNode(x_103, x_104, x_79);
x_106 = l_Lean_Parser_mergeOrElseErrors(x_105, x_74, x_71);
lean_dec(x_71);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_83);
lean_dec(x_1);
x_107 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_108 = l_Lean_Parser_ParserState_mkNode(x_82, x_107, x_79);
x_109 = l_Lean_Parser_mergeOrElseErrors(x_108, x_74, x_71);
lean_dec(x_71);
return x_109;
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_36);
lean_dec(x_4);
x_110 = lean_ctor_get(x_5, 0);
lean_inc(x_110);
lean_dec(x_5);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_array_get_size(x_111);
lean_dec(x_111);
x_113 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_114 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_115 = l_Lean_Parser_nonReservedSymbolFnAux(x_113, x_114, x_1, x_110);
x_116 = lean_ctor_get(x_115, 3);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_array_get_size(x_117);
lean_dec(x_117);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
x_120 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_115);
x_121 = lean_ctor_get(x_120, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_119);
x_122 = l_Lean_nullKind;
x_123 = l_Lean_Parser_ParserState_mkNode(x_120, x_122, x_118);
x_124 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_125 = l_Lean_Parser_ParserState_mkNode(x_123, x_124, x_112);
return x_125;
}
else
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_121);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
x_127 = lean_nat_dec_eq(x_126, x_119);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_119);
x_128 = l_Lean_nullKind;
x_129 = l_Lean_Parser_ParserState_mkNode(x_120, x_128, x_118);
x_130 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_131 = l_Lean_Parser_ParserState_mkNode(x_129, x_130, x_112);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = l_Lean_Parser_ParserState_restore(x_120, x_118, x_119);
x_133 = l_Lean_nullKind;
x_134 = l_Lean_Parser_ParserState_mkNode(x_132, x_133, x_118);
x_135 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_136 = l_Lean_Parser_ParserState_mkNode(x_134, x_135, x_112);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_116);
lean_dec(x_1);
x_137 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_138 = l_Lean_Parser_ParserState_mkNode(x_115, x_137, x_112);
return x_138;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_ident_x27;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_optionaInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__1;
x_2 = l_Lean_Parser_Tactic_intro___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_intro___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_intro___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_intro___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intro___closed__5;
x_2 = l_Lean_Parser_Tactic_intro___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intro() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_intro___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_intro;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Parser_manyAux___main___closed__1;
x_12 = l_Lean_Parser_ParserState_mkUnexpectedError(x_6, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intros");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_intros___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intros ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_3 = l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_86);
lean_inc(x_1);
x_90 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_90;
goto block_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 2);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_92);
x_5 = x_93;
goto block_85;
}
block_85:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_12);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_15);
x_19 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_1);
x_21 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_12, x_21, x_9);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_27 = lean_string_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_31 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_32 = l_Lean_Parser_nonReservedSymbolFnAux(x_30, x_31, x_1, x_24);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_32);
x_37 = l_Lean_nullKind;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_35);
x_39 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_29);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_1);
x_41 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_32, x_41, x_29);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_1);
x_46 = lean_apply_2(x_4, x_1, x_24);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_45);
x_51 = l_Lean_Parser_ParserState_restore(x_46, x_44, x_45);
lean_dec(x_44);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_array_get_size(x_52);
lean_dec(x_52);
x_54 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_55 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_56 = l_Lean_Parser_nonReservedSymbolFnAux(x_54, x_55, x_1, x_51);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_array_get_size(x_58);
lean_dec(x_58);
x_60 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_56);
x_61 = l_Lean_nullKind;
x_62 = l_Lean_Parser_ParserState_mkNode(x_60, x_61, x_59);
x_63 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_64 = l_Lean_Parser_ParserState_mkNode(x_62, x_63, x_53);
x_65 = l_Lean_Parser_mergeOrElseErrors(x_64, x_48, x_45);
lean_dec(x_45);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_1);
x_66 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_67 = l_Lean_Parser_ParserState_mkNode(x_56, x_66, x_53);
x_68 = l_Lean_Parser_mergeOrElseErrors(x_67, x_48, x_45);
lean_dec(x_45);
return x_68;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_23);
lean_dec(x_4);
x_69 = lean_ctor_get(x_5, 0);
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_array_get_size(x_70);
lean_dec(x_70);
x_72 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_73 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_74 = l_Lean_Parser_nonReservedSymbolFnAux(x_72, x_73, x_1, x_69);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_array_get_size(x_76);
lean_dec(x_76);
x_78 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_74);
x_79 = l_Lean_nullKind;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_77);
x_81 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_82 = l_Lean_Parser_ParserState_mkNode(x_80, x_81, x_71);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_75);
lean_dec(x_1);
x_83 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_84 = l_Lean_Parser_ParserState_mkNode(x_74, x_83, x_71);
return x_84;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_ident_x27;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intros___closed__1;
x_2 = l_Lean_Parser_Tactic_intros___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_intros___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_intros___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_intros___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_intros___closed__5;
x_2 = l_Lean_Parser_Tactic_intros___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_intros() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_intros___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_intros;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assumption");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_3 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_inc(x_1);
x_57 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_57;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
x_5 = x_60;
goto block_52;
}
block_52:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_11 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_23 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_24 = l_Lean_Parser_nonReservedSymbolFnAux(x_22, x_23, x_1, x_16);
x_25 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_16);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_33, x_29);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_39 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_37);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_32, x_29);
lean_dec(x_29);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_15);
lean_dec(x_4);
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_48 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_49 = l_Lean_Parser_nonReservedSymbolFnAux(x_47, x_48, x_1, x_44);
x_50 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_46);
return x_51;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_assumption___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_assumption___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_assumption___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_assumption___closed__3;
x_2 = l_Lean_Parser_Tactic_assumption___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_assumption() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_assumption___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_assumption;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_apply___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_apply___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_3 = l_Lean_Parser_Tactic_apply___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_nat_dec_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_inc(x_1);
x_82 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_82;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
x_5 = x_85;
goto block_77;
}
block_77:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_termParser___closed__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_29 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_30 = l_Lean_Parser_nonReservedSymbolFnAux(x_28, x_29, x_1, x_22);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Parser_termParser___closed__2;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Parser_categoryParser___elambda__1(x_32, x_33, x_1, x_30);
x_35 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_1);
x_37 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_30, x_37, x_27);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = lean_apply_2(x_4, x_1, x_22);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_nat_dec_eq(x_45, x_41);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_41);
x_47 = l_Lean_Parser_ParserState_restore(x_42, x_40, x_41);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_51 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_52 = l_Lean_Parser_nonReservedSymbolFnAux(x_50, x_51, x_1, x_47);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Parser_termParser___closed__2;
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Parser_categoryParser___elambda__1(x_54, x_55, x_1, x_52);
x_57 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_49);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_44, x_41);
lean_dec(x_41);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_dec(x_1);
x_60 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_52, x_60, x_49);
x_62 = l_Lean_Parser_mergeOrElseErrors(x_61, x_44, x_41);
lean_dec(x_41);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_21);
lean_dec(x_4);
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_67 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_68 = l_Lean_Parser_nonReservedSymbolFnAux(x_66, x_67, x_1, x_63);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Parser_termParser___closed__2;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Parser_categoryParser___elambda__1(x_70, x_71, x_1, x_68);
x_73 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_1);
x_75 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_68, x_75, x_65);
return x_76;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_apply___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_apply___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_apply___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_apply___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_apply___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_apply___closed__4;
x_2 = l_Lean_Parser_Tactic_apply___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_apply() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_apply___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_apply;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("exact");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_exact___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_exact___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("exact ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_exact___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_3 = l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_nat_dec_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_inc(x_1);
x_82 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_82;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
x_5 = x_85;
goto block_77;
}
block_77:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_termParser___closed__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_29 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_30 = l_Lean_Parser_nonReservedSymbolFnAux(x_28, x_29, x_1, x_22);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Parser_termParser___closed__2;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Parser_categoryParser___elambda__1(x_32, x_33, x_1, x_30);
x_35 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_1);
x_37 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_30, x_37, x_27);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = lean_apply_2(x_4, x_1, x_22);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_nat_dec_eq(x_45, x_41);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_41);
x_47 = l_Lean_Parser_ParserState_restore(x_42, x_40, x_41);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_51 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_52 = l_Lean_Parser_nonReservedSymbolFnAux(x_50, x_51, x_1, x_47);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Parser_termParser___closed__2;
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Parser_categoryParser___elambda__1(x_54, x_55, x_1, x_52);
x_57 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_49);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_44, x_41);
lean_dec(x_41);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_dec(x_1);
x_60 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_52, x_60, x_49);
x_62 = l_Lean_Parser_mergeOrElseErrors(x_61, x_44, x_41);
lean_dec(x_41);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_21);
lean_dec(x_4);
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_67 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_68 = l_Lean_Parser_nonReservedSymbolFnAux(x_66, x_67, x_1, x_63);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Parser_termParser___closed__2;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Parser_categoryParser___elambda__1(x_70, x_71, x_1, x_68);
x_73 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_1);
x_75 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_68, x_75, x_65);
return x_76;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_exact___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_exact___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_exact___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_exact___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_exact___closed__4;
x_2 = l_Lean_Parser_Tactic_exact___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_exact() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_exact___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_exact(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_exact;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refine");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_refine___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_refine___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refine ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_refine___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_3 = l_Lean_Parser_Tactic_refine___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_nat_dec_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_inc(x_1);
x_82 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_82;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
x_5 = x_85;
goto block_77;
}
block_77:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_termParser___closed__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_29 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_30 = l_Lean_Parser_nonReservedSymbolFnAux(x_28, x_29, x_1, x_22);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Parser_termParser___closed__2;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Parser_categoryParser___elambda__1(x_32, x_33, x_1, x_30);
x_35 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_1);
x_37 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_30, x_37, x_27);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = lean_apply_2(x_4, x_1, x_22);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_nat_dec_eq(x_45, x_41);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_41);
x_47 = l_Lean_Parser_ParserState_restore(x_42, x_40, x_41);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_51 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_52 = l_Lean_Parser_nonReservedSymbolFnAux(x_50, x_51, x_1, x_47);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Parser_termParser___closed__2;
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Parser_categoryParser___elambda__1(x_54, x_55, x_1, x_52);
x_57 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_49);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_44, x_41);
lean_dec(x_41);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_dec(x_1);
x_60 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_52, x_60, x_49);
x_62 = l_Lean_Parser_mergeOrElseErrors(x_61, x_44, x_41);
lean_dec(x_41);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_21);
lean_dec(x_4);
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_67 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_68 = l_Lean_Parser_nonReservedSymbolFnAux(x_66, x_67, x_1, x_63);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Parser_termParser___closed__2;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Parser_categoryParser___elambda__1(x_70, x_71, x_1, x_68);
x_73 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_1);
x_75 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_68, x_75, x_65);
return x_76;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_refine___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_refine___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_refine___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_refine___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_refine___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_refine___closed__4;
x_2 = l_Lean_Parser_Tactic_refine___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_refine() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_refine___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_refine(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_refine;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_case___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_case___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_case___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_3 = l_Lean_Parser_Tactic_case___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_95 = lean_ctor_get(x_2, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
x_98 = lean_nat_dec_eq(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_95);
lean_inc(x_1);
x_99 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_99;
goto block_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 2);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_101);
x_5 = x_102;
goto block_94;
}
block_94:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_11 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = l_Lean_Parser_ident___elambda__1(x_1, x_12);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Parser_categoryParser___elambda__1(x_16, x_17, x_1, x_14);
x_19 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_1);
x_21 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_14, x_21, x_9);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_1);
x_23 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_12, x_23, x_9);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_29 = lean_string_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_33 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_34 = l_Lean_Parser_nonReservedSymbolFnAux(x_32, x_33, x_1, x_26);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_inc(x_1);
x_36 = l_Lean_Parser_ident___elambda__1(x_1, x_34);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Parser_categoryParser___elambda__1(x_38, x_39, x_1, x_36);
x_41 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_31);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_1);
x_43 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_44 = l_Lean_Parser_ParserState_mkNode(x_36, x_43, x_31);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_1);
x_45 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_46 = l_Lean_Parser_ParserState_mkNode(x_34, x_45, x_31);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_1);
x_50 = lean_apply_2(x_4, x_1, x_26);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_nat_dec_eq(x_53, x_49);
lean_dec(x_53);
if (x_54 == 0)
{
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_inc(x_49);
x_55 = l_Lean_Parser_ParserState_restore(x_50, x_48, x_49);
lean_dec(x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_array_get_size(x_56);
lean_dec(x_56);
x_58 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_59 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_60 = l_Lean_Parser_nonReservedSymbolFnAux(x_58, x_59, x_1, x_55);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_inc(x_1);
x_62 = l_Lean_Parser_ident___elambda__1(x_1, x_60);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Parser_categoryParser___elambda__1(x_64, x_65, x_1, x_62);
x_67 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_68 = l_Lean_Parser_ParserState_mkNode(x_66, x_67, x_57);
x_69 = l_Lean_Parser_mergeOrElseErrors(x_68, x_52, x_49);
lean_dec(x_49);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_63);
lean_dec(x_1);
x_70 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_71 = l_Lean_Parser_ParserState_mkNode(x_62, x_70, x_57);
x_72 = l_Lean_Parser_mergeOrElseErrors(x_71, x_52, x_49);
lean_dec(x_49);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_1);
x_73 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_60, x_73, x_57);
x_75 = l_Lean_Parser_mergeOrElseErrors(x_74, x_52, x_49);
lean_dec(x_49);
return x_75;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_25);
lean_dec(x_4);
x_76 = lean_ctor_get(x_5, 0);
lean_inc(x_76);
lean_dec(x_5);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_array_get_size(x_77);
lean_dec(x_77);
x_79 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_80 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_81 = l_Lean_Parser_nonReservedSymbolFnAux(x_79, x_80, x_1, x_76);
x_82 = lean_ctor_get(x_81, 3);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_inc(x_1);
x_83 = l_Lean_Parser_ident___elambda__1(x_1, x_81);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Parser_categoryParser___elambda__1(x_85, x_86, x_1, x_83);
x_88 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_89 = l_Lean_Parser_ParserState_mkNode(x_87, x_88, x_78);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
lean_dec(x_1);
x_90 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_91 = l_Lean_Parser_ParserState_mkNode(x_83, x_90, x_78);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
lean_dec(x_1);
x_92 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_93 = l_Lean_Parser_ParserState_mkNode(x_81, x_92, x_78);
return x_93;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_seq___closed__1;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_case___closed__1;
x_2 = l_Lean_Parser_Tactic_case___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_case___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_case___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_case___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_case___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_case___closed__5;
x_2 = l_Lean_Parser_Tactic_case___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_case() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_case___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_case(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_case;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("allGoals");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("allGoals ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_3 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_nat_dec_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_inc(x_1);
x_82 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_82;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
x_5 = x_85;
goto block_77;
}
block_77:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_11 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_29 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_30 = l_Lean_Parser_nonReservedSymbolFnAux(x_28, x_29, x_1, x_22);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Parser_categoryParser___elambda__1(x_32, x_33, x_1, x_30);
x_35 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_1);
x_37 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_30, x_37, x_27);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = lean_apply_2(x_4, x_1, x_22);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_nat_dec_eq(x_45, x_41);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_41);
x_47 = l_Lean_Parser_ParserState_restore(x_42, x_40, x_41);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_51 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_52 = l_Lean_Parser_nonReservedSymbolFnAux(x_50, x_51, x_1, x_47);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Parser_categoryParser___elambda__1(x_54, x_55, x_1, x_52);
x_57 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_49);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_44, x_41);
lean_dec(x_41);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_dec(x_1);
x_60 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_52, x_60, x_49);
x_62 = l_Lean_Parser_mergeOrElseErrors(x_61, x_44, x_41);
lean_dec(x_41);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_21);
lean_dec(x_4);
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_67 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_68 = l_Lean_Parser_nonReservedSymbolFnAux(x_66, x_67, x_1, x_63);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Parser_categoryParser___elambda__1(x_70, x_71, x_1, x_68);
x_73 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_1);
x_75 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_68, x_75, x_65);
return x_76;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_allGoals___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_allGoals___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_allGoals___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_allGoals___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_allGoals___closed__4;
x_2 = l_Lean_Parser_Tactic_allGoals___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_allGoals() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_allGoals___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_allGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_allGoals;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_skip___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_skip___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_3 = l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_inc(x_1);
x_57 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_57;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
x_5 = x_60;
goto block_52;
}
block_52:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_11 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_23 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_24 = l_Lean_Parser_nonReservedSymbolFnAux(x_22, x_23, x_1, x_16);
x_25 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_16);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_33, x_29);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_39 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_37);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_32, x_29);
lean_dec(x_29);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_15);
lean_dec(x_4);
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_48 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_49 = l_Lean_Parser_nonReservedSymbolFnAux(x_47, x_48, x_1, x_44);
x_50 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_46);
return x_51;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_skip___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_skip___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_skip___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_skip___closed__3;
x_2 = l_Lean_Parser_Tactic_skip___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_skip() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_skip___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_skip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_skip;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("traceState");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_3 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_inc(x_1);
x_57 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_57;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
x_5 = x_60;
goto block_52;
}
block_52:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_11 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_12 = l_Lean_Parser_nonReservedSymbolFnAux(x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_23 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_24 = l_Lean_Parser_nonReservedSymbolFnAux(x_22, x_23, x_1, x_16);
x_25 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_16);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_33, x_29);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_39 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_37);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_32, x_29);
lean_dec(x_29);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_15);
lean_dec(x_4);
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_48 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_49 = l_Lean_Parser_nonReservedSymbolFnAux(x_47, x_48, x_1, x_44);
x_50 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_46);
return x_51;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_traceState___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_traceState___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_traceState___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_traceState___closed__3;
x_2 = l_Lean_Parser_Tactic_traceState___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_traceState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_traceState___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_traceState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_traceState;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_paren___elambda__1___closed__2;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_paren___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_3 = l_Lean_Parser_Tactic_paren___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_313 = lean_ctor_get(x_2, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 1);
lean_inc(x_315);
x_316 = lean_nat_dec_eq(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
lean_inc(x_1);
x_317 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_317;
goto block_312;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 2);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_2);
lean_ctor_set(x_320, 1, x_319);
x_5 = x_320;
goto block_312;
}
block_312:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = l_Lean_Parser_tokenFn(x_1, x_7);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 2)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_48 = lean_string_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_49, x_41);
x_10 = x_50;
goto block_40;
}
else
{
lean_dec(x_41);
x_10 = x_42;
goto block_40;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_51, x_41);
x_10 = x_52;
goto block_40;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_43);
x_53 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_53, x_41);
x_10 = x_54;
goto block_40;
}
block_40:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_Parser_tokenFn(x_1, x_12);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_22, x_14);
x_24 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_15, x_26, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_28 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_28, x_14);
x_30 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_32 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_32, x_14);
x_34 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_37 = l_Lean_Parser_ParserState_mkNode(x_12, x_36, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_39 = l_Lean_Parser_ParserState_mkNode(x_10, x_38, x_9);
return x_39;
}
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
lean_dec(x_6);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_90 = lean_ctor_get(x_56, 1);
lean_inc(x_90);
lean_inc(x_1);
x_91 = l_Lean_Parser_tokenFn(x_1, x_56);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_93);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 2)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_97 = lean_string_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_99 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_98, x_90);
x_59 = x_99;
goto block_89;
}
else
{
lean_dec(x_90);
x_59 = x_91;
goto block_89;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_101 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_100, x_90);
x_59 = x_101;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_92);
x_102 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_103 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_102, x_90);
x_59 = x_103;
goto block_89;
}
block_89:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_1);
x_61 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_59);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = l_Lean_Parser_tokenFn(x_1, x_61);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 2)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_70 = lean_string_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_71, x_63);
x_73 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_58);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_76 = l_Lean_Parser_ParserState_mkNode(x_64, x_75, x_58);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_77 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_78 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_77, x_63);
x_79 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_58);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
x_81 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_82 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_81, x_63);
x_83 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_58);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
lean_dec(x_1);
x_85 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_86 = l_Lean_Parser_ParserState_mkNode(x_61, x_85, x_58);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_87 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_88 = l_Lean_Parser_ParserState_mkNode(x_59, x_87, x_58);
return x_88;
}
}
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_55);
lean_dec(x_4);
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_138 = lean_ctor_get(x_104, 1);
lean_inc(x_138);
lean_inc(x_1);
x_139 = l_Lean_Parser_tokenFn(x_1, x_104);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_141);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 2)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_145 = lean_string_dec_eq(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_147 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_146, x_138);
x_107 = x_147;
goto block_137;
}
else
{
lean_dec(x_138);
x_107 = x_139;
goto block_137;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
x_148 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_149 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_148, x_138);
x_107 = x_149;
goto block_137;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
x_150 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_151 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_150, x_138);
x_107 = x_151;
goto block_137;
}
block_137:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_inc(x_1);
x_109 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_107);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Parser_tokenFn(x_1, x_109);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 2)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_118 = lean_string_dec_eq(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_119, x_111);
x_121 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_122 = l_Lean_Parser_ParserState_mkNode(x_120, x_121, x_106);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_111);
x_123 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_124 = l_Lean_Parser_ParserState_mkNode(x_112, x_123, x_106);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
x_125 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_126 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_125, x_111);
x_127 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_128 = l_Lean_Parser_ParserState_mkNode(x_126, x_127, x_106);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_113);
x_129 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_130 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_129, x_111);
x_131 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_132 = l_Lean_Parser_ParserState_mkNode(x_130, x_131, x_106);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_110);
lean_dec(x_1);
x_133 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_134 = l_Lean_Parser_ParserState_mkNode(x_109, x_133, x_106);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_108);
lean_dec(x_1);
x_135 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_136 = l_Lean_Parser_ParserState_mkNode(x_107, x_135, x_106);
return x_136;
}
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_5, 0);
lean_inc(x_152);
lean_dec(x_5);
x_153 = lean_ctor_get(x_55, 1);
lean_inc(x_153);
lean_dec(x_55);
x_154 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_155 = lean_string_dec_eq(x_153, x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_4);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_array_get_size(x_156);
lean_dec(x_156);
x_189 = lean_ctor_get(x_152, 1);
lean_inc(x_189);
lean_inc(x_1);
x_190 = l_Lean_Parser_tokenFn(x_1, x_152);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 2)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_196 = lean_string_dec_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_198 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_197, x_189);
x_158 = x_198;
goto block_188;
}
else
{
lean_dec(x_189);
x_158 = x_190;
goto block_188;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
x_199 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_200 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_199, x_189);
x_158 = x_200;
goto block_188;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_191);
x_201 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_202 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_201, x_189);
x_158 = x_202;
goto block_188;
}
block_188:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_1);
x_160 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_158);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = l_Lean_Parser_tokenFn(x_1, x_160);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_165);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 2)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_169 = lean_string_dec_eq(x_167, x_168);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_171 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_170, x_162);
x_172 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_173 = l_Lean_Parser_ParserState_mkNode(x_171, x_172, x_157);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
x_174 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_175 = l_Lean_Parser_ParserState_mkNode(x_163, x_174, x_157);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_166);
x_176 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_177 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_176, x_162);
x_178 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_179 = l_Lean_Parser_ParserState_mkNode(x_177, x_178, x_157);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_164);
x_180 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_181 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_180, x_162);
x_182 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_183 = l_Lean_Parser_ParserState_mkNode(x_181, x_182, x_157);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_161);
lean_dec(x_1);
x_184 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_185 = l_Lean_Parser_ParserState_mkNode(x_160, x_184, x_157);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_1);
x_186 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_187 = l_Lean_Parser_ParserState_mkNode(x_158, x_186, x_157);
return x_187;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
x_204 = lean_array_get_size(x_203);
lean_dec(x_203);
x_205 = lean_ctor_get(x_152, 1);
lean_inc(x_205);
lean_inc(x_1);
x_206 = lean_apply_2(x_4, x_1, x_152);
x_207 = lean_ctor_get(x_206, 3);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
x_210 = lean_nat_dec_eq(x_209, x_205);
lean_dec(x_209);
if (x_210 == 0)
{
lean_dec(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_251; lean_object* x_252; 
lean_inc(x_205);
x_211 = l_Lean_Parser_ParserState_restore(x_206, x_204, x_205);
lean_dec(x_204);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_array_get_size(x_212);
lean_dec(x_212);
lean_inc(x_1);
x_251 = l_Lean_Parser_tokenFn(x_1, x_211);
x_252 = lean_ctor_get(x_251, 3);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 2)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_257 = lean_string_dec_eq(x_255, x_256);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_205);
x_259 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_258, x_205);
x_214 = x_259;
goto block_250;
}
else
{
x_214 = x_251;
goto block_250;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_254);
x_260 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_205);
x_261 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_260, x_205);
x_214 = x_261;
goto block_250;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_252);
x_262 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_205);
x_263 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_262, x_205);
x_214 = x_263;
goto block_250;
}
block_250:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 3);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_inc(x_1);
x_216 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_214);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = l_Lean_Parser_tokenFn(x_1, x_216);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_221);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 2)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_225 = lean_string_dec_eq(x_223, x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_227 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_226, x_218);
x_228 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_229 = l_Lean_Parser_ParserState_mkNode(x_227, x_228, x_213);
x_230 = l_Lean_Parser_mergeOrElseErrors(x_229, x_208, x_205);
lean_dec(x_205);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_218);
x_231 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_232 = l_Lean_Parser_ParserState_mkNode(x_219, x_231, x_213);
x_233 = l_Lean_Parser_mergeOrElseErrors(x_232, x_208, x_205);
lean_dec(x_205);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_222);
x_234 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_235 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_234, x_218);
x_236 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_237 = l_Lean_Parser_ParserState_mkNode(x_235, x_236, x_213);
x_238 = l_Lean_Parser_mergeOrElseErrors(x_237, x_208, x_205);
lean_dec(x_205);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_220);
x_239 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_240 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_239, x_218);
x_241 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_242 = l_Lean_Parser_ParserState_mkNode(x_240, x_241, x_213);
x_243 = l_Lean_Parser_mergeOrElseErrors(x_242, x_208, x_205);
lean_dec(x_205);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_217);
lean_dec(x_1);
x_244 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_245 = l_Lean_Parser_ParserState_mkNode(x_216, x_244, x_213);
x_246 = l_Lean_Parser_mergeOrElseErrors(x_245, x_208, x_205);
lean_dec(x_205);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_215);
lean_dec(x_1);
x_247 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_248 = l_Lean_Parser_ParserState_mkNode(x_214, x_247, x_213);
x_249 = l_Lean_Parser_mergeOrElseErrors(x_248, x_208, x_205);
lean_dec(x_205);
return x_249;
}
}
}
}
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_55);
lean_dec(x_4);
x_264 = lean_ctor_get(x_5, 0);
lean_inc(x_264);
lean_dec(x_5);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_array_get_size(x_265);
lean_dec(x_265);
x_298 = lean_ctor_get(x_264, 1);
lean_inc(x_298);
lean_inc(x_1);
x_299 = l_Lean_Parser_tokenFn(x_1, x_264);
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 2)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_305 = lean_string_dec_eq(x_303, x_304);
lean_dec(x_303);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_307 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_306, x_298);
x_267 = x_307;
goto block_297;
}
else
{
lean_dec(x_298);
x_267 = x_299;
goto block_297;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_302);
x_308 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_309 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_308, x_298);
x_267 = x_309;
goto block_297;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_300);
x_310 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_311 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_310, x_298);
x_267 = x_311;
goto block_297;
}
block_297:
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_inc(x_1);
x_269 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_267);
x_270 = lean_ctor_get(x_269, 3);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_272 = l_Lean_Parser_tokenFn(x_1, x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_274);
lean_dec(x_274);
if (lean_obj_tag(x_275) == 2)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_278 = lean_string_dec_eq(x_276, x_277);
lean_dec(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_280 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_279, x_271);
x_281 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_282 = l_Lean_Parser_ParserState_mkNode(x_280, x_281, x_266);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_283 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_284 = l_Lean_Parser_ParserState_mkNode(x_272, x_283, x_266);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_275);
x_285 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_286 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_285, x_271);
x_287 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_288 = l_Lean_Parser_ParserState_mkNode(x_286, x_287, x_266);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_273);
x_289 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_290 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_289, x_271);
x_291 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_292 = l_Lean_Parser_ParserState_mkNode(x_290, x_291, x_266);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_270);
lean_dec(x_1);
x_293 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_294 = l_Lean_Parser_ParserState_mkNode(x_269, x_293, x_266);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_268);
lean_dec(x_1);
x_295 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_296 = l_Lean_Parser_ParserState_mkNode(x_267, x_295, x_266);
return x_296;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nonEmptySeq;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__5;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__1;
x_2 = l_Lean_Parser_Tactic_paren___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_paren___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_paren___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_paren___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_paren___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_paren___closed__4;
x_2 = l_Lean_Parser_Tactic_paren___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_paren___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_paren;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nestedTacticBlock");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("begin ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_313 = lean_ctor_get(x_2, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 1);
lean_inc(x_315);
x_316 = lean_nat_dec_eq(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
lean_inc(x_1);
x_317 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_317;
goto block_312;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 2);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_2);
lean_ctor_set(x_320, 1, x_319);
x_5 = x_320;
goto block_312;
}
block_312:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = l_Lean_Parser_tokenFn(x_1, x_7);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 2)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_48 = lean_string_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_49, x_41);
x_10 = x_50;
goto block_40;
}
else
{
lean_dec(x_41);
x_10 = x_42;
goto block_40;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_51, x_41);
x_10 = x_52;
goto block_40;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_43);
x_53 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_53, x_41);
x_10 = x_54;
goto block_40;
}
block_40:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_Parser_tokenFn(x_1, x_12);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_22, x_14);
x_24 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_15, x_26, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_28 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_28, x_14);
x_30 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_32 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_32, x_14);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_12, x_36, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_10, x_38, x_9);
return x_39;
}
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
lean_dec(x_6);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_90 = lean_ctor_get(x_56, 1);
lean_inc(x_90);
lean_inc(x_1);
x_91 = l_Lean_Parser_tokenFn(x_1, x_56);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_93);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 2)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_97 = lean_string_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_99 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_98, x_90);
x_59 = x_99;
goto block_89;
}
else
{
lean_dec(x_90);
x_59 = x_91;
goto block_89;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_101 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_100, x_90);
x_59 = x_101;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_92);
x_102 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_103 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_102, x_90);
x_59 = x_103;
goto block_89;
}
block_89:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_1);
x_61 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_59);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = l_Lean_Parser_tokenFn(x_1, x_61);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 2)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_70 = lean_string_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_71, x_63);
x_73 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_58);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_64, x_75, x_58);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_77 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_78 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_77, x_63);
x_79 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_58);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
x_81 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_82 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_81, x_63);
x_83 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_58);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
lean_dec(x_1);
x_85 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_86 = l_Lean_Parser_ParserState_mkNode(x_61, x_85, x_58);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_87 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_88 = l_Lean_Parser_ParserState_mkNode(x_59, x_87, x_58);
return x_88;
}
}
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_55);
lean_dec(x_4);
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_138 = lean_ctor_get(x_104, 1);
lean_inc(x_138);
lean_inc(x_1);
x_139 = l_Lean_Parser_tokenFn(x_1, x_104);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_141);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 2)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_145 = lean_string_dec_eq(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_147 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_146, x_138);
x_107 = x_147;
goto block_137;
}
else
{
lean_dec(x_138);
x_107 = x_139;
goto block_137;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
x_148 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_149 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_148, x_138);
x_107 = x_149;
goto block_137;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
x_150 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_151 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_150, x_138);
x_107 = x_151;
goto block_137;
}
block_137:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_inc(x_1);
x_109 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_107);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Parser_tokenFn(x_1, x_109);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 2)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_118 = lean_string_dec_eq(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_119, x_111);
x_121 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_122 = l_Lean_Parser_ParserState_mkNode(x_120, x_121, x_106);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_111);
x_123 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_124 = l_Lean_Parser_ParserState_mkNode(x_112, x_123, x_106);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
x_125 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_126 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_125, x_111);
x_127 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_128 = l_Lean_Parser_ParserState_mkNode(x_126, x_127, x_106);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_113);
x_129 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_130 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_129, x_111);
x_131 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_132 = l_Lean_Parser_ParserState_mkNode(x_130, x_131, x_106);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_110);
lean_dec(x_1);
x_133 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_109, x_133, x_106);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_108);
lean_dec(x_1);
x_135 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_136 = l_Lean_Parser_ParserState_mkNode(x_107, x_135, x_106);
return x_136;
}
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_5, 0);
lean_inc(x_152);
lean_dec(x_5);
x_153 = lean_ctor_get(x_55, 1);
lean_inc(x_153);
lean_dec(x_55);
x_154 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_155 = lean_string_dec_eq(x_153, x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_4);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_array_get_size(x_156);
lean_dec(x_156);
x_189 = lean_ctor_get(x_152, 1);
lean_inc(x_189);
lean_inc(x_1);
x_190 = l_Lean_Parser_tokenFn(x_1, x_152);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 2)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_196 = lean_string_dec_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_198 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_197, x_189);
x_158 = x_198;
goto block_188;
}
else
{
lean_dec(x_189);
x_158 = x_190;
goto block_188;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
x_199 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_200 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_199, x_189);
x_158 = x_200;
goto block_188;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_191);
x_201 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_202 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_201, x_189);
x_158 = x_202;
goto block_188;
}
block_188:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_1);
x_160 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_158);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = l_Lean_Parser_tokenFn(x_1, x_160);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_165);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 2)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_169 = lean_string_dec_eq(x_167, x_168);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_171 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_170, x_162);
x_172 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_173 = l_Lean_Parser_ParserState_mkNode(x_171, x_172, x_157);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
x_174 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_175 = l_Lean_Parser_ParserState_mkNode(x_163, x_174, x_157);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_166);
x_176 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_177 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_176, x_162);
x_178 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_179 = l_Lean_Parser_ParserState_mkNode(x_177, x_178, x_157);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_164);
x_180 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_181 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_180, x_162);
x_182 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_183 = l_Lean_Parser_ParserState_mkNode(x_181, x_182, x_157);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_161);
lean_dec(x_1);
x_184 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_185 = l_Lean_Parser_ParserState_mkNode(x_160, x_184, x_157);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_1);
x_186 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_187 = l_Lean_Parser_ParserState_mkNode(x_158, x_186, x_157);
return x_187;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
x_204 = lean_array_get_size(x_203);
lean_dec(x_203);
x_205 = lean_ctor_get(x_152, 1);
lean_inc(x_205);
lean_inc(x_1);
x_206 = lean_apply_2(x_4, x_1, x_152);
x_207 = lean_ctor_get(x_206, 3);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
x_210 = lean_nat_dec_eq(x_209, x_205);
lean_dec(x_209);
if (x_210 == 0)
{
lean_dec(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_251; lean_object* x_252; 
lean_inc(x_205);
x_211 = l_Lean_Parser_ParserState_restore(x_206, x_204, x_205);
lean_dec(x_204);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_array_get_size(x_212);
lean_dec(x_212);
lean_inc(x_1);
x_251 = l_Lean_Parser_tokenFn(x_1, x_211);
x_252 = lean_ctor_get(x_251, 3);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 2)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_257 = lean_string_dec_eq(x_255, x_256);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_259 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_258, x_205);
x_214 = x_259;
goto block_250;
}
else
{
x_214 = x_251;
goto block_250;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_254);
x_260 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_261 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_260, x_205);
x_214 = x_261;
goto block_250;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_252);
x_262 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_263 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_262, x_205);
x_214 = x_263;
goto block_250;
}
block_250:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 3);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_inc(x_1);
x_216 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_214);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = l_Lean_Parser_tokenFn(x_1, x_216);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_221);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 2)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_225 = lean_string_dec_eq(x_223, x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_227 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_226, x_218);
x_228 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_229 = l_Lean_Parser_ParserState_mkNode(x_227, x_228, x_213);
x_230 = l_Lean_Parser_mergeOrElseErrors(x_229, x_208, x_205);
lean_dec(x_205);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_218);
x_231 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_232 = l_Lean_Parser_ParserState_mkNode(x_219, x_231, x_213);
x_233 = l_Lean_Parser_mergeOrElseErrors(x_232, x_208, x_205);
lean_dec(x_205);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_222);
x_234 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_235 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_234, x_218);
x_236 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_237 = l_Lean_Parser_ParserState_mkNode(x_235, x_236, x_213);
x_238 = l_Lean_Parser_mergeOrElseErrors(x_237, x_208, x_205);
lean_dec(x_205);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_220);
x_239 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_240 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_239, x_218);
x_241 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_242 = l_Lean_Parser_ParserState_mkNode(x_240, x_241, x_213);
x_243 = l_Lean_Parser_mergeOrElseErrors(x_242, x_208, x_205);
lean_dec(x_205);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_217);
lean_dec(x_1);
x_244 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_245 = l_Lean_Parser_ParserState_mkNode(x_216, x_244, x_213);
x_246 = l_Lean_Parser_mergeOrElseErrors(x_245, x_208, x_205);
lean_dec(x_205);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_215);
lean_dec(x_1);
x_247 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_248 = l_Lean_Parser_ParserState_mkNode(x_214, x_247, x_213);
x_249 = l_Lean_Parser_mergeOrElseErrors(x_248, x_208, x_205);
lean_dec(x_205);
return x_249;
}
}
}
}
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_55);
lean_dec(x_4);
x_264 = lean_ctor_get(x_5, 0);
lean_inc(x_264);
lean_dec(x_5);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_array_get_size(x_265);
lean_dec(x_265);
x_298 = lean_ctor_get(x_264, 1);
lean_inc(x_298);
lean_inc(x_1);
x_299 = l_Lean_Parser_tokenFn(x_1, x_264);
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 2)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_305 = lean_string_dec_eq(x_303, x_304);
lean_dec(x_303);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_307 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_306, x_298);
x_267 = x_307;
goto block_297;
}
else
{
lean_dec(x_298);
x_267 = x_299;
goto block_297;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_302);
x_308 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_309 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_308, x_298);
x_267 = x_309;
goto block_297;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_300);
x_310 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_311 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_310, x_298);
x_267 = x_311;
goto block_297;
}
block_297:
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_inc(x_1);
x_269 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_267);
x_270 = lean_ctor_get(x_269, 3);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_272 = l_Lean_Parser_tokenFn(x_1, x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_274);
lean_dec(x_274);
if (lean_obj_tag(x_275) == 2)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_278 = lean_string_dec_eq(x_276, x_277);
lean_dec(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_280 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_279, x_271);
x_281 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_282 = l_Lean_Parser_ParserState_mkNode(x_280, x_281, x_266);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_283 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_284 = l_Lean_Parser_ParserState_mkNode(x_272, x_283, x_266);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_275);
x_285 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_286 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_285, x_271);
x_287 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_288 = l_Lean_Parser_ParserState_mkNode(x_286, x_287, x_266);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_273);
x_289 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_290 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_289, x_271);
x_291 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_292 = l_Lean_Parser_ParserState_mkNode(x_290, x_291, x_266);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_270);
lean_dec(x_1);
x_293 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_294 = l_Lean_Parser_ParserState_mkNode(x_269, x_293, x_266);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_268);
lean_dec(x_1);
x_295 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_296 = l_Lean_Parser_ParserState_mkNode(x_267, x_295, x_266);
return x_296;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__6;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__8;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_nestedTacticBlock;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nestedTacticBlockCurly");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_313 = lean_ctor_get(x_2, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 1);
lean_inc(x_315);
x_316 = lean_nat_dec_eq(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
lean_inc(x_1);
x_317 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_317;
goto block_312;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 2);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_2);
lean_ctor_set(x_320, 1, x_319);
x_5 = x_320;
goto block_312;
}
block_312:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = l_Lean_Parser_tokenFn(x_1, x_7);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 2)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_48 = lean_string_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_49, x_41);
x_10 = x_50;
goto block_40;
}
else
{
lean_dec(x_41);
x_10 = x_42;
goto block_40;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_51, x_41);
x_10 = x_52;
goto block_40;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_43);
x_53 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_53, x_41);
x_10 = x_54;
goto block_40;
}
block_40:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_Parser_tokenFn(x_1, x_12);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_22, x_14);
x_24 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_15, x_26, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_28 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_28, x_14);
x_30 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_32 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_32, x_14);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_12, x_36, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_10, x_38, x_9);
return x_39;
}
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
lean_dec(x_6);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_90 = lean_ctor_get(x_56, 1);
lean_inc(x_90);
lean_inc(x_1);
x_91 = l_Lean_Parser_tokenFn(x_1, x_56);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_93);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 2)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_97 = lean_string_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_99 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_98, x_90);
x_59 = x_99;
goto block_89;
}
else
{
lean_dec(x_90);
x_59 = x_91;
goto block_89;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_101 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_100, x_90);
x_59 = x_101;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_92);
x_102 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_103 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_102, x_90);
x_59 = x_103;
goto block_89;
}
block_89:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_1);
x_61 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_59);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = l_Lean_Parser_tokenFn(x_1, x_61);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 2)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_70 = lean_string_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_71, x_63);
x_73 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_58);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_64, x_75, x_58);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_77 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_78 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_77, x_63);
x_79 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_58);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
x_81 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_82 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_81, x_63);
x_83 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_58);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
lean_dec(x_1);
x_85 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_86 = l_Lean_Parser_ParserState_mkNode(x_61, x_85, x_58);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_87 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_88 = l_Lean_Parser_ParserState_mkNode(x_59, x_87, x_58);
return x_88;
}
}
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_55);
lean_dec(x_4);
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_138 = lean_ctor_get(x_104, 1);
lean_inc(x_138);
lean_inc(x_1);
x_139 = l_Lean_Parser_tokenFn(x_1, x_104);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_141);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 2)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_145 = lean_string_dec_eq(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_147 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_146, x_138);
x_107 = x_147;
goto block_137;
}
else
{
lean_dec(x_138);
x_107 = x_139;
goto block_137;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
x_148 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_149 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_148, x_138);
x_107 = x_149;
goto block_137;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
x_150 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_151 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_150, x_138);
x_107 = x_151;
goto block_137;
}
block_137:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_inc(x_1);
x_109 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_107);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Parser_tokenFn(x_1, x_109);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 2)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_118 = lean_string_dec_eq(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_119, x_111);
x_121 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_122 = l_Lean_Parser_ParserState_mkNode(x_120, x_121, x_106);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_111);
x_123 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_124 = l_Lean_Parser_ParserState_mkNode(x_112, x_123, x_106);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
x_125 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_126 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_125, x_111);
x_127 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_128 = l_Lean_Parser_ParserState_mkNode(x_126, x_127, x_106);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_113);
x_129 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_130 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_129, x_111);
x_131 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_132 = l_Lean_Parser_ParserState_mkNode(x_130, x_131, x_106);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_110);
lean_dec(x_1);
x_133 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_109, x_133, x_106);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_108);
lean_dec(x_1);
x_135 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_136 = l_Lean_Parser_ParserState_mkNode(x_107, x_135, x_106);
return x_136;
}
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_5, 0);
lean_inc(x_152);
lean_dec(x_5);
x_153 = lean_ctor_get(x_55, 1);
lean_inc(x_153);
lean_dec(x_55);
x_154 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_155 = lean_string_dec_eq(x_153, x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_4);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_array_get_size(x_156);
lean_dec(x_156);
x_189 = lean_ctor_get(x_152, 1);
lean_inc(x_189);
lean_inc(x_1);
x_190 = l_Lean_Parser_tokenFn(x_1, x_152);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 2)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_196 = lean_string_dec_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_198 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_197, x_189);
x_158 = x_198;
goto block_188;
}
else
{
lean_dec(x_189);
x_158 = x_190;
goto block_188;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
x_199 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_200 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_199, x_189);
x_158 = x_200;
goto block_188;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_191);
x_201 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_202 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_201, x_189);
x_158 = x_202;
goto block_188;
}
block_188:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_1);
x_160 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_158);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = l_Lean_Parser_tokenFn(x_1, x_160);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_165);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 2)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_169 = lean_string_dec_eq(x_167, x_168);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_171 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_170, x_162);
x_172 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_173 = l_Lean_Parser_ParserState_mkNode(x_171, x_172, x_157);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
x_174 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_175 = l_Lean_Parser_ParserState_mkNode(x_163, x_174, x_157);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_166);
x_176 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_177 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_176, x_162);
x_178 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_179 = l_Lean_Parser_ParserState_mkNode(x_177, x_178, x_157);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_164);
x_180 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_181 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_180, x_162);
x_182 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_183 = l_Lean_Parser_ParserState_mkNode(x_181, x_182, x_157);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_161);
lean_dec(x_1);
x_184 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_185 = l_Lean_Parser_ParserState_mkNode(x_160, x_184, x_157);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_1);
x_186 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_187 = l_Lean_Parser_ParserState_mkNode(x_158, x_186, x_157);
return x_187;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
x_204 = lean_array_get_size(x_203);
lean_dec(x_203);
x_205 = lean_ctor_get(x_152, 1);
lean_inc(x_205);
lean_inc(x_1);
x_206 = lean_apply_2(x_4, x_1, x_152);
x_207 = lean_ctor_get(x_206, 3);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
x_210 = lean_nat_dec_eq(x_209, x_205);
lean_dec(x_209);
if (x_210 == 0)
{
lean_dec(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_251; lean_object* x_252; 
lean_inc(x_205);
x_211 = l_Lean_Parser_ParserState_restore(x_206, x_204, x_205);
lean_dec(x_204);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_array_get_size(x_212);
lean_dec(x_212);
lean_inc(x_1);
x_251 = l_Lean_Parser_tokenFn(x_1, x_211);
x_252 = lean_ctor_get(x_251, 3);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 2)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_257 = lean_string_dec_eq(x_255, x_256);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_205);
x_259 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_258, x_205);
x_214 = x_259;
goto block_250;
}
else
{
x_214 = x_251;
goto block_250;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_254);
x_260 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_205);
x_261 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_260, x_205);
x_214 = x_261;
goto block_250;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_252);
x_262 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_205);
x_263 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_262, x_205);
x_214 = x_263;
goto block_250;
}
block_250:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 3);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_inc(x_1);
x_216 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_214);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = l_Lean_Parser_tokenFn(x_1, x_216);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_221);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 2)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_225 = lean_string_dec_eq(x_223, x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_227 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_226, x_218);
x_228 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_229 = l_Lean_Parser_ParserState_mkNode(x_227, x_228, x_213);
x_230 = l_Lean_Parser_mergeOrElseErrors(x_229, x_208, x_205);
lean_dec(x_205);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_218);
x_231 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_232 = l_Lean_Parser_ParserState_mkNode(x_219, x_231, x_213);
x_233 = l_Lean_Parser_mergeOrElseErrors(x_232, x_208, x_205);
lean_dec(x_205);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_222);
x_234 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_235 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_234, x_218);
x_236 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_237 = l_Lean_Parser_ParserState_mkNode(x_235, x_236, x_213);
x_238 = l_Lean_Parser_mergeOrElseErrors(x_237, x_208, x_205);
lean_dec(x_205);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_220);
x_239 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_240 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_239, x_218);
x_241 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_242 = l_Lean_Parser_ParserState_mkNode(x_240, x_241, x_213);
x_243 = l_Lean_Parser_mergeOrElseErrors(x_242, x_208, x_205);
lean_dec(x_205);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_217);
lean_dec(x_1);
x_244 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_245 = l_Lean_Parser_ParserState_mkNode(x_216, x_244, x_213);
x_246 = l_Lean_Parser_mergeOrElseErrors(x_245, x_208, x_205);
lean_dec(x_205);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_215);
lean_dec(x_1);
x_247 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_248 = l_Lean_Parser_ParserState_mkNode(x_214, x_247, x_213);
x_249 = l_Lean_Parser_mergeOrElseErrors(x_248, x_208, x_205);
lean_dec(x_205);
return x_249;
}
}
}
}
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_55);
lean_dec(x_4);
x_264 = lean_ctor_get(x_5, 0);
lean_inc(x_264);
lean_dec(x_5);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_array_get_size(x_265);
lean_dec(x_265);
x_298 = lean_ctor_get(x_264, 1);
lean_inc(x_298);
lean_inc(x_1);
x_299 = l_Lean_Parser_tokenFn(x_1, x_264);
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 2)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_305 = lean_string_dec_eq(x_303, x_304);
lean_dec(x_303);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_307 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_306, x_298);
x_267 = x_307;
goto block_297;
}
else
{
lean_dec(x_298);
x_267 = x_299;
goto block_297;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_302);
x_308 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_309 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_308, x_298);
x_267 = x_309;
goto block_297;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_300);
x_310 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_311 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_310, x_298);
x_267 = x_311;
goto block_297;
}
block_297:
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_inc(x_1);
x_269 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_267);
x_270 = lean_ctor_get(x_269, 3);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_272 = l_Lean_Parser_tokenFn(x_1, x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_274);
lean_dec(x_274);
if (lean_obj_tag(x_275) == 2)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_278 = lean_string_dec_eq(x_276, x_277);
lean_dec(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_280 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_279, x_271);
x_281 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_282 = l_Lean_Parser_ParserState_mkNode(x_280, x_281, x_266);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_283 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_284 = l_Lean_Parser_ParserState_mkNode(x_272, x_283, x_266);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_275);
x_285 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_286 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_285, x_271);
x_287 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_288 = l_Lean_Parser_ParserState_mkNode(x_286, x_287, x_266);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_273);
x_289 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_290 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_289, x_271);
x_291 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_292 = l_Lean_Parser_ParserState_mkNode(x_290, x_291, x_266);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_270);
lean_dec(x_1);
x_293 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_294 = l_Lean_Parser_ParserState_mkNode(x_269, x_293, x_266);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_268);
lean_dec(x_1);
x_295 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_296 = l_Lean_Parser_ParserState_mkNode(x_267, x_295, x_266);
return x_296;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_explicitUniv___closed__4;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_subtype___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_nestedTacticBlockCurly;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_orelse___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_orelse___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_Parser_tokenFn(x_1, x_2);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
x_22 = lean_string_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_16, x_23, x_15);
x_5 = x_24;
goto block_14;
}
else
{
lean_dec(x_15);
x_5 = x_16;
goto block_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_25 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_26 = l_Lean_Parser_ParserState_mkErrorsAt(x_16, x_25, x_15);
x_5 = x_26;
goto block_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_27 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_28 = l_Lean_Parser_ParserState_mkErrorsAt(x_16, x_27, x_15);
x_5 = x_28;
goto block_14;
}
block_14:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Parser_categoryParser___elambda__1(x_7, x_8, x_1, x_5);
x_10 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_11 = l_Lean_Parser_ParserState_mkTrailingNode(x_9, x_10, x_4);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_1);
x_12 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkTrailingNode(x_5, x_12, x_4);
lean_dec(x_4);
return x_13;
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_orelse___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_orelse___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_orelse___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_orelse___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_orelse___closed__4;
x_2 = l_Lean_Parser_Tactic_orelse___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_orelse___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_4 = 0;
x_5 = l_Lean_Parser_Tactic_orelse;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticBlock");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_313 = lean_ctor_get(x_2, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 1);
lean_inc(x_315);
x_316 = lean_nat_dec_eq(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
lean_inc(x_1);
x_317 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_317;
goto block_312;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 2);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_2);
lean_ctor_set(x_320, 1, x_319);
x_5 = x_320;
goto block_312;
}
block_312:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_1);
x_42 = l_Lean_Parser_tokenFn(x_1, x_7);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 2)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_48 = lean_string_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_49, x_41);
x_10 = x_50;
goto block_40;
}
else
{
lean_dec(x_41);
x_10 = x_42;
goto block_40;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_51 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_51, x_41);
x_10 = x_52;
goto block_40;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_43);
x_53 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_42, x_53, x_41);
x_10 = x_54;
goto block_40;
}
block_40:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_Parser_tokenFn(x_1, x_12);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_22, x_14);
x_24 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_15, x_26, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_28 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_28, x_14);
x_30 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_32 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_32, x_14);
x_34 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_1);
x_36 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_12, x_36, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_10, x_38, x_9);
return x_39;
}
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
lean_dec(x_6);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_90 = lean_ctor_get(x_56, 1);
lean_inc(x_90);
lean_inc(x_1);
x_91 = l_Lean_Parser_tokenFn(x_1, x_56);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_93);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 2)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_97 = lean_string_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_99 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_98, x_90);
x_59 = x_99;
goto block_89;
}
else
{
lean_dec(x_90);
x_59 = x_91;
goto block_89;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_101 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_100, x_90);
x_59 = x_101;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_92);
x_102 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_103 = l_Lean_Parser_ParserState_mkErrorsAt(x_91, x_102, x_90);
x_59 = x_103;
goto block_89;
}
block_89:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_1);
x_61 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_59);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = l_Lean_Parser_tokenFn(x_1, x_61);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 2)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_70 = lean_string_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_71, x_63);
x_73 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_74 = l_Lean_Parser_ParserState_mkNode(x_72, x_73, x_58);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_76 = l_Lean_Parser_ParserState_mkNode(x_64, x_75, x_58);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_77 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_78 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_77, x_63);
x_79 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_58);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
x_81 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_82 = l_Lean_Parser_ParserState_mkErrorsAt(x_64, x_81, x_63);
x_83 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_58);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
lean_dec(x_1);
x_85 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_86 = l_Lean_Parser_ParserState_mkNode(x_61, x_85, x_58);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_87 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_88 = l_Lean_Parser_ParserState_mkNode(x_59, x_87, x_58);
return x_88;
}
}
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_55);
lean_dec(x_4);
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_138 = lean_ctor_get(x_104, 1);
lean_inc(x_138);
lean_inc(x_1);
x_139 = l_Lean_Parser_tokenFn(x_1, x_104);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_141);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 2)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_145 = lean_string_dec_eq(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_147 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_146, x_138);
x_107 = x_147;
goto block_137;
}
else
{
lean_dec(x_138);
x_107 = x_139;
goto block_137;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
x_148 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_149 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_148, x_138);
x_107 = x_149;
goto block_137;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
x_150 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_151 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_150, x_138);
x_107 = x_151;
goto block_137;
}
block_137:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_inc(x_1);
x_109 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_107);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Parser_tokenFn(x_1, x_109);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 2)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_118 = lean_string_dec_eq(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_119, x_111);
x_121 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_122 = l_Lean_Parser_ParserState_mkNode(x_120, x_121, x_106);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_111);
x_123 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_124 = l_Lean_Parser_ParserState_mkNode(x_112, x_123, x_106);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
x_125 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_126 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_125, x_111);
x_127 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_128 = l_Lean_Parser_ParserState_mkNode(x_126, x_127, x_106);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_113);
x_129 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_130 = l_Lean_Parser_ParserState_mkErrorsAt(x_112, x_129, x_111);
x_131 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_132 = l_Lean_Parser_ParserState_mkNode(x_130, x_131, x_106);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_110);
lean_dec(x_1);
x_133 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_109, x_133, x_106);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_108);
lean_dec(x_1);
x_135 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_136 = l_Lean_Parser_ParserState_mkNode(x_107, x_135, x_106);
return x_136;
}
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_5, 0);
lean_inc(x_152);
lean_dec(x_5);
x_153 = lean_ctor_get(x_55, 1);
lean_inc(x_153);
lean_dec(x_55);
x_154 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_155 = lean_string_dec_eq(x_153, x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_4);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_array_get_size(x_156);
lean_dec(x_156);
x_189 = lean_ctor_get(x_152, 1);
lean_inc(x_189);
lean_inc(x_1);
x_190 = l_Lean_Parser_tokenFn(x_1, x_152);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 2)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_196 = lean_string_dec_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_198 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_197, x_189);
x_158 = x_198;
goto block_188;
}
else
{
lean_dec(x_189);
x_158 = x_190;
goto block_188;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
x_199 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_200 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_199, x_189);
x_158 = x_200;
goto block_188;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_191);
x_201 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_202 = l_Lean_Parser_ParserState_mkErrorsAt(x_190, x_201, x_189);
x_158 = x_202;
goto block_188;
}
block_188:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_1);
x_160 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_158);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = l_Lean_Parser_tokenFn(x_1, x_160);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_165);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 2)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_169 = lean_string_dec_eq(x_167, x_168);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_171 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_170, x_162);
x_172 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_173 = l_Lean_Parser_ParserState_mkNode(x_171, x_172, x_157);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
x_174 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_175 = l_Lean_Parser_ParserState_mkNode(x_163, x_174, x_157);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_166);
x_176 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_177 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_176, x_162);
x_178 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_179 = l_Lean_Parser_ParserState_mkNode(x_177, x_178, x_157);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_164);
x_180 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_181 = l_Lean_Parser_ParserState_mkErrorsAt(x_163, x_180, x_162);
x_182 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_183 = l_Lean_Parser_ParserState_mkNode(x_181, x_182, x_157);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_161);
lean_dec(x_1);
x_184 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_185 = l_Lean_Parser_ParserState_mkNode(x_160, x_184, x_157);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
lean_dec(x_1);
x_186 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_187 = l_Lean_Parser_ParserState_mkNode(x_158, x_186, x_157);
return x_187;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
x_204 = lean_array_get_size(x_203);
lean_dec(x_203);
x_205 = lean_ctor_get(x_152, 1);
lean_inc(x_205);
lean_inc(x_1);
x_206 = lean_apply_2(x_4, x_1, x_152);
x_207 = lean_ctor_get(x_206, 3);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
x_210 = lean_nat_dec_eq(x_209, x_205);
lean_dec(x_209);
if (x_210 == 0)
{
lean_dec(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_1);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_251; lean_object* x_252; 
lean_inc(x_205);
x_211 = l_Lean_Parser_ParserState_restore(x_206, x_204, x_205);
lean_dec(x_204);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_array_get_size(x_212);
lean_dec(x_212);
lean_inc(x_1);
x_251 = l_Lean_Parser_tokenFn(x_1, x_211);
x_252 = lean_ctor_get(x_251, 3);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 2)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_257 = lean_string_dec_eq(x_255, x_256);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_259 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_258, x_205);
x_214 = x_259;
goto block_250;
}
else
{
x_214 = x_251;
goto block_250;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_254);
x_260 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_261 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_260, x_205);
x_214 = x_261;
goto block_250;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_252);
x_262 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_205);
x_263 = l_Lean_Parser_ParserState_mkErrorsAt(x_251, x_262, x_205);
x_214 = x_263;
goto block_250;
}
block_250:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 3);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_inc(x_1);
x_216 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_214);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = l_Lean_Parser_tokenFn(x_1, x_216);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_221);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 2)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_225 = lean_string_dec_eq(x_223, x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_227 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_226, x_218);
x_228 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_229 = l_Lean_Parser_ParserState_mkNode(x_227, x_228, x_213);
x_230 = l_Lean_Parser_mergeOrElseErrors(x_229, x_208, x_205);
lean_dec(x_205);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_218);
x_231 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_232 = l_Lean_Parser_ParserState_mkNode(x_219, x_231, x_213);
x_233 = l_Lean_Parser_mergeOrElseErrors(x_232, x_208, x_205);
lean_dec(x_205);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_222);
x_234 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_235 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_234, x_218);
x_236 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_237 = l_Lean_Parser_ParserState_mkNode(x_235, x_236, x_213);
x_238 = l_Lean_Parser_mergeOrElseErrors(x_237, x_208, x_205);
lean_dec(x_205);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_220);
x_239 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_240 = l_Lean_Parser_ParserState_mkErrorsAt(x_219, x_239, x_218);
x_241 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_242 = l_Lean_Parser_ParserState_mkNode(x_240, x_241, x_213);
x_243 = l_Lean_Parser_mergeOrElseErrors(x_242, x_208, x_205);
lean_dec(x_205);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_217);
lean_dec(x_1);
x_244 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_245 = l_Lean_Parser_ParserState_mkNode(x_216, x_244, x_213);
x_246 = l_Lean_Parser_mergeOrElseErrors(x_245, x_208, x_205);
lean_dec(x_205);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_215);
lean_dec(x_1);
x_247 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_248 = l_Lean_Parser_ParserState_mkNode(x_214, x_247, x_213);
x_249 = l_Lean_Parser_mergeOrElseErrors(x_248, x_208, x_205);
lean_dec(x_205);
return x_249;
}
}
}
}
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_55);
lean_dec(x_4);
x_264 = lean_ctor_get(x_5, 0);
lean_inc(x_264);
lean_dec(x_5);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_array_get_size(x_265);
lean_dec(x_265);
x_298 = lean_ctor_get(x_264, 1);
lean_inc(x_298);
lean_inc(x_1);
x_299 = l_Lean_Parser_tokenFn(x_1, x_264);
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 2)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_305 = lean_string_dec_eq(x_303, x_304);
lean_dec(x_303);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_307 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_306, x_298);
x_267 = x_307;
goto block_297;
}
else
{
lean_dec(x_298);
x_267 = x_299;
goto block_297;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_302);
x_308 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_309 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_308, x_298);
x_267 = x_309;
goto block_297;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_300);
x_310 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_311 = l_Lean_Parser_ParserState_mkErrorsAt(x_299, x_310, x_298);
x_267 = x_311;
goto block_297;
}
block_297:
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_inc(x_1);
x_269 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_267);
x_270 = lean_ctor_get(x_269, 3);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_272 = l_Lean_Parser_tokenFn(x_1, x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_274);
lean_dec(x_274);
if (lean_obj_tag(x_275) == 2)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_278 = lean_string_dec_eq(x_276, x_277);
lean_dec(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_280 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_279, x_271);
x_281 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_282 = l_Lean_Parser_ParserState_mkNode(x_280, x_281, x_266);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_283 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_284 = l_Lean_Parser_ParserState_mkNode(x_272, x_283, x_266);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_275);
x_285 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_286 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_285, x_271);
x_287 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_288 = l_Lean_Parser_ParserState_mkNode(x_286, x_287, x_266);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_273);
x_289 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_290 = l_Lean_Parser_ParserState_mkErrorsAt(x_272, x_289, x_271);
x_291 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_292 = l_Lean_Parser_ParserState_mkNode(x_290, x_291, x_266);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_270);
lean_dec(x_1);
x_293 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_294 = l_Lean_Parser_ParserState_mkNode(x_269, x_293, x_266);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_268);
lean_dec(x_1);
x_295 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_296 = l_Lean_Parser_ParserState_mkNode(x_267, x_295, x_266);
return x_296;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__1;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_tacticBlock___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticBlock___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__4;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_termParser___closed__2;
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_tacticBlock;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stxQuot");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`(tactic|");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_1);
x_38 = l_Lean_Parser_tokenFn(x_1, x_2);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 2)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4;
x_44 = lean_string_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7;
x_46 = l_Lean_Parser_ParserState_mkErrorsAt(x_38, x_45, x_37);
x_5 = x_46;
goto block_36;
}
else
{
lean_dec(x_37);
x_5 = x_38;
goto block_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
x_47 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_38, x_47, x_37);
x_5 = x_48;
goto block_36;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
x_49 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_38, x_49, x_37);
x_5 = x_50;
goto block_36;
}
block_36:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_7, x_7, x_1, x_5);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = l_Lean_Parser_tokenFn(x_1, x_8);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_17 = lean_string_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_18, x_10);
x_20 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_11, x_22, x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_24 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_24, x_10);
x_26 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_4);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_28 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_28, x_10);
x_30 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_4);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_1);
x_32 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_8, x_32, x_4);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_5, x_34, x_4);
return x_35;
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___closed__2;
x_2 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__5;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___closed__1;
x_2 = l_Lean_Parser_Term_tacticStxQuot___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_tacticStxQuot___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticStxQuot___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___closed__4;
x_2 = l_Lean_Parser_Term_tacticStxQuot___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___closed__6;
return x_1;
}
}
lean_object* _init_l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticStxQuot");
return x_1;
}
}
lean_object* _init_l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_termParser___closed__2;
x_3 = l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_tacticStxQuot;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Tactic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__1);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__2);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__3);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinTacticParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regTacticParserAttribute___closed__1 = _init_l_Lean_Parser_regTacticParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regTacticParserAttribute___closed__1);
l_Lean_Parser_regTacticParserAttribute___closed__2 = _init_l_Lean_Parser_regTacticParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regTacticParserAttribute___closed__2);
res = l_Lean_Parser_regTacticParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_underscoreFn___closed__1 = _init_l_Lean_Parser_Tactic_underscoreFn___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___closed__1);
l_Lean_Parser_Tactic_underscoreFn___closed__2 = _init_l_Lean_Parser_Tactic_underscoreFn___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___closed__2);
l_Lean_Parser_Tactic_underscoreFn___closed__3 = _init_l_Lean_Parser_Tactic_underscoreFn___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___closed__3);
l_Lean_Parser_Tactic_underscoreFn___closed__4 = _init_l_Lean_Parser_Tactic_underscoreFn___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___closed__4);
l_Lean_Parser_Tactic_underscore___closed__1 = _init_l_Lean_Parser_Tactic_underscore___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_underscore___closed__1);
l_Lean_Parser_Tactic_underscore___closed__2 = _init_l_Lean_Parser_Tactic_underscore___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_underscore___closed__2);
l_Lean_Parser_Tactic_underscore = _init_l_Lean_Parser_Tactic_underscore();
lean_mark_persistent(l_Lean_Parser_Tactic_underscore);
l_Lean_Parser_Tactic_ident_x27___closed__1 = _init_l_Lean_Parser_Tactic_ident_x27___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_ident_x27___closed__1);
l_Lean_Parser_Tactic_ident_x27___closed__2 = _init_l_Lean_Parser_Tactic_ident_x27___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_ident_x27___closed__2);
l_Lean_Parser_Tactic_ident_x27___closed__3 = _init_l_Lean_Parser_Tactic_ident_x27___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_ident_x27___closed__3);
l_Lean_Parser_Tactic_ident_x27 = _init_l_Lean_Parser_Tactic_ident_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_ident_x27);
l_Lean_Parser_Tactic_seq___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___elambda__1___closed__1);
l_Lean_Parser_Tactic_seq___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___elambda__1___closed__2);
l_Lean_Parser_Tactic_seq___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___elambda__1___closed__3);
l_Lean_Parser_Tactic_seq___closed__1 = _init_l_Lean_Parser_Tactic_seq___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__1);
l_Lean_Parser_Tactic_seq___closed__2 = _init_l_Lean_Parser_Tactic_seq___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__2);
l_Lean_Parser_Tactic_seq___closed__3 = _init_l_Lean_Parser_Tactic_seq___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__3);
l_Lean_Parser_Tactic_seq___closed__4 = _init_l_Lean_Parser_Tactic_seq___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__4);
l_Lean_Parser_Tactic_seq___closed__5 = _init_l_Lean_Parser_Tactic_seq___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__5);
l_Lean_Parser_Tactic_seq = _init_l_Lean_Parser_Tactic_seq();
lean_mark_persistent(l_Lean_Parser_Tactic_seq);
l_Lean_Parser_Tactic_nonEmptySeq___closed__1 = _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nonEmptySeq___closed__1);
l_Lean_Parser_Tactic_nonEmptySeq___closed__2 = _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nonEmptySeq___closed__2);
l_Lean_Parser_Tactic_nonEmptySeq = _init_l_Lean_Parser_Tactic_nonEmptySeq();
lean_mark_persistent(l_Lean_Parser_Tactic_nonEmptySeq);
l_Lean_Parser_Tactic_intro___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__1);
l_Lean_Parser_Tactic_intro___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__2);
l_Lean_Parser_Tactic_intro___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__3);
l_Lean_Parser_Tactic_intro___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__4);
l_Lean_Parser_Tactic_intro___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__5);
l_Lean_Parser_Tactic_intro___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__6);
l_Lean_Parser_Tactic_intro___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__7);
l_Lean_Parser_Tactic_intro___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_intro___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___elambda__1___closed__8);
l_Lean_Parser_Tactic_intro___closed__1 = _init_l_Lean_Parser_Tactic_intro___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__1);
l_Lean_Parser_Tactic_intro___closed__2 = _init_l_Lean_Parser_Tactic_intro___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__2);
l_Lean_Parser_Tactic_intro___closed__3 = _init_l_Lean_Parser_Tactic_intro___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__3);
l_Lean_Parser_Tactic_intro___closed__4 = _init_l_Lean_Parser_Tactic_intro___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__4);
l_Lean_Parser_Tactic_intro___closed__5 = _init_l_Lean_Parser_Tactic_intro___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__5);
l_Lean_Parser_Tactic_intro___closed__6 = _init_l_Lean_Parser_Tactic_intro___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__6);
l_Lean_Parser_Tactic_intro___closed__7 = _init_l_Lean_Parser_Tactic_intro___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_intro___closed__7);
l_Lean_Parser_Tactic_intro = _init_l_Lean_Parser_Tactic_intro();
lean_mark_persistent(l_Lean_Parser_Tactic_intro);
res = l___regBuiltinParser_Lean_Parser_Tactic_intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_intros___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__1);
l_Lean_Parser_Tactic_intros___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__2);
l_Lean_Parser_Tactic_intros___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__3);
l_Lean_Parser_Tactic_intros___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__4);
l_Lean_Parser_Tactic_intros___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__5);
l_Lean_Parser_Tactic_intros___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__6);
l_Lean_Parser_Tactic_intros___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__7);
l_Lean_Parser_Tactic_intros___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_intros___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___elambda__1___closed__8);
l_Lean_Parser_Tactic_intros___closed__1 = _init_l_Lean_Parser_Tactic_intros___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__1);
l_Lean_Parser_Tactic_intros___closed__2 = _init_l_Lean_Parser_Tactic_intros___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__2);
l_Lean_Parser_Tactic_intros___closed__3 = _init_l_Lean_Parser_Tactic_intros___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__3);
l_Lean_Parser_Tactic_intros___closed__4 = _init_l_Lean_Parser_Tactic_intros___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__4);
l_Lean_Parser_Tactic_intros___closed__5 = _init_l_Lean_Parser_Tactic_intros___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__5);
l_Lean_Parser_Tactic_intros___closed__6 = _init_l_Lean_Parser_Tactic_intros___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__6);
l_Lean_Parser_Tactic_intros___closed__7 = _init_l_Lean_Parser_Tactic_intros___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_intros___closed__7);
l_Lean_Parser_Tactic_intros = _init_l_Lean_Parser_Tactic_intros();
lean_mark_persistent(l_Lean_Parser_Tactic_intros);
res = l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__1);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__2);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__3);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__4);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__5);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__6);
l_Lean_Parser_Tactic_assumption___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_assumption___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___elambda__1___closed__7);
l_Lean_Parser_Tactic_assumption___closed__1 = _init_l_Lean_Parser_Tactic_assumption___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___closed__1);
l_Lean_Parser_Tactic_assumption___closed__2 = _init_l_Lean_Parser_Tactic_assumption___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___closed__2);
l_Lean_Parser_Tactic_assumption___closed__3 = _init_l_Lean_Parser_Tactic_assumption___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___closed__3);
l_Lean_Parser_Tactic_assumption___closed__4 = _init_l_Lean_Parser_Tactic_assumption___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___closed__4);
l_Lean_Parser_Tactic_assumption___closed__5 = _init_l_Lean_Parser_Tactic_assumption___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption___closed__5);
l_Lean_Parser_Tactic_assumption = _init_l_Lean_Parser_Tactic_assumption();
lean_mark_persistent(l_Lean_Parser_Tactic_assumption);
res = l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_apply___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__1);
l_Lean_Parser_Tactic_apply___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__2);
l_Lean_Parser_Tactic_apply___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__3);
l_Lean_Parser_Tactic_apply___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__4);
l_Lean_Parser_Tactic_apply___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__5);
l_Lean_Parser_Tactic_apply___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__6);
l_Lean_Parser_Tactic_apply___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__7);
l_Lean_Parser_Tactic_apply___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_apply___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___elambda__1___closed__8);
l_Lean_Parser_Tactic_apply___closed__1 = _init_l_Lean_Parser_Tactic_apply___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__1);
l_Lean_Parser_Tactic_apply___closed__2 = _init_l_Lean_Parser_Tactic_apply___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__2);
l_Lean_Parser_Tactic_apply___closed__3 = _init_l_Lean_Parser_Tactic_apply___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__3);
l_Lean_Parser_Tactic_apply___closed__4 = _init_l_Lean_Parser_Tactic_apply___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__4);
l_Lean_Parser_Tactic_apply___closed__5 = _init_l_Lean_Parser_Tactic_apply___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__5);
l_Lean_Parser_Tactic_apply___closed__6 = _init_l_Lean_Parser_Tactic_apply___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_apply___closed__6);
l_Lean_Parser_Tactic_apply = _init_l_Lean_Parser_Tactic_apply();
lean_mark_persistent(l_Lean_Parser_Tactic_apply);
res = l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_exact___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__1);
l_Lean_Parser_Tactic_exact___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__2);
l_Lean_Parser_Tactic_exact___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__3);
l_Lean_Parser_Tactic_exact___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__4);
l_Lean_Parser_Tactic_exact___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__5);
l_Lean_Parser_Tactic_exact___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__6);
l_Lean_Parser_Tactic_exact___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__7);
l_Lean_Parser_Tactic_exact___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_exact___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___elambda__1___closed__8);
l_Lean_Parser_Tactic_exact___closed__1 = _init_l_Lean_Parser_Tactic_exact___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__1);
l_Lean_Parser_Tactic_exact___closed__2 = _init_l_Lean_Parser_Tactic_exact___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__2);
l_Lean_Parser_Tactic_exact___closed__3 = _init_l_Lean_Parser_Tactic_exact___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__3);
l_Lean_Parser_Tactic_exact___closed__4 = _init_l_Lean_Parser_Tactic_exact___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__4);
l_Lean_Parser_Tactic_exact___closed__5 = _init_l_Lean_Parser_Tactic_exact___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__5);
l_Lean_Parser_Tactic_exact___closed__6 = _init_l_Lean_Parser_Tactic_exact___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_exact___closed__6);
l_Lean_Parser_Tactic_exact = _init_l_Lean_Parser_Tactic_exact();
lean_mark_persistent(l_Lean_Parser_Tactic_exact);
res = l___regBuiltinParser_Lean_Parser_Tactic_exact(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_refine___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__1);
l_Lean_Parser_Tactic_refine___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__2);
l_Lean_Parser_Tactic_refine___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__3);
l_Lean_Parser_Tactic_refine___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__4);
l_Lean_Parser_Tactic_refine___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__5);
l_Lean_Parser_Tactic_refine___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__6);
l_Lean_Parser_Tactic_refine___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__7);
l_Lean_Parser_Tactic_refine___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_refine___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___elambda__1___closed__8);
l_Lean_Parser_Tactic_refine___closed__1 = _init_l_Lean_Parser_Tactic_refine___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__1);
l_Lean_Parser_Tactic_refine___closed__2 = _init_l_Lean_Parser_Tactic_refine___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__2);
l_Lean_Parser_Tactic_refine___closed__3 = _init_l_Lean_Parser_Tactic_refine___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__3);
l_Lean_Parser_Tactic_refine___closed__4 = _init_l_Lean_Parser_Tactic_refine___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__4);
l_Lean_Parser_Tactic_refine___closed__5 = _init_l_Lean_Parser_Tactic_refine___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__5);
l_Lean_Parser_Tactic_refine___closed__6 = _init_l_Lean_Parser_Tactic_refine___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_refine___closed__6);
l_Lean_Parser_Tactic_refine = _init_l_Lean_Parser_Tactic_refine();
lean_mark_persistent(l_Lean_Parser_Tactic_refine);
res = l___regBuiltinParser_Lean_Parser_Tactic_refine(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_case___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__1);
l_Lean_Parser_Tactic_case___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__2);
l_Lean_Parser_Tactic_case___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__3);
l_Lean_Parser_Tactic_case___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__4);
l_Lean_Parser_Tactic_case___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__5);
l_Lean_Parser_Tactic_case___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__6);
l_Lean_Parser_Tactic_case___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_case___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_case___elambda__1___closed__7);
l_Lean_Parser_Tactic_case___closed__1 = _init_l_Lean_Parser_Tactic_case___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__1);
l_Lean_Parser_Tactic_case___closed__2 = _init_l_Lean_Parser_Tactic_case___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__2);
l_Lean_Parser_Tactic_case___closed__3 = _init_l_Lean_Parser_Tactic_case___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__3);
l_Lean_Parser_Tactic_case___closed__4 = _init_l_Lean_Parser_Tactic_case___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__4);
l_Lean_Parser_Tactic_case___closed__5 = _init_l_Lean_Parser_Tactic_case___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__5);
l_Lean_Parser_Tactic_case___closed__6 = _init_l_Lean_Parser_Tactic_case___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__6);
l_Lean_Parser_Tactic_case___closed__7 = _init_l_Lean_Parser_Tactic_case___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_case___closed__7);
l_Lean_Parser_Tactic_case = _init_l_Lean_Parser_Tactic_case();
lean_mark_persistent(l_Lean_Parser_Tactic_case);
res = l___regBuiltinParser_Lean_Parser_Tactic_case(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7);
l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8);
l_Lean_Parser_Tactic_allGoals___closed__1 = _init_l_Lean_Parser_Tactic_allGoals___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__1);
l_Lean_Parser_Tactic_allGoals___closed__2 = _init_l_Lean_Parser_Tactic_allGoals___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__2);
l_Lean_Parser_Tactic_allGoals___closed__3 = _init_l_Lean_Parser_Tactic_allGoals___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__3);
l_Lean_Parser_Tactic_allGoals___closed__4 = _init_l_Lean_Parser_Tactic_allGoals___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__4);
l_Lean_Parser_Tactic_allGoals___closed__5 = _init_l_Lean_Parser_Tactic_allGoals___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__5);
l_Lean_Parser_Tactic_allGoals___closed__6 = _init_l_Lean_Parser_Tactic_allGoals___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals___closed__6);
l_Lean_Parser_Tactic_allGoals = _init_l_Lean_Parser_Tactic_allGoals();
lean_mark_persistent(l_Lean_Parser_Tactic_allGoals);
res = l___regBuiltinParser_Lean_Parser_Tactic_allGoals(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_skip___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__1);
l_Lean_Parser_Tactic_skip___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__2);
l_Lean_Parser_Tactic_skip___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__3);
l_Lean_Parser_Tactic_skip___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__4);
l_Lean_Parser_Tactic_skip___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__5);
l_Lean_Parser_Tactic_skip___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__6);
l_Lean_Parser_Tactic_skip___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_skip___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___elambda__1___closed__7);
l_Lean_Parser_Tactic_skip___closed__1 = _init_l_Lean_Parser_Tactic_skip___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___closed__1);
l_Lean_Parser_Tactic_skip___closed__2 = _init_l_Lean_Parser_Tactic_skip___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___closed__2);
l_Lean_Parser_Tactic_skip___closed__3 = _init_l_Lean_Parser_Tactic_skip___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___closed__3);
l_Lean_Parser_Tactic_skip___closed__4 = _init_l_Lean_Parser_Tactic_skip___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___closed__4);
l_Lean_Parser_Tactic_skip___closed__5 = _init_l_Lean_Parser_Tactic_skip___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_skip___closed__5);
l_Lean_Parser_Tactic_skip = _init_l_Lean_Parser_Tactic_skip();
lean_mark_persistent(l_Lean_Parser_Tactic_skip);
res = l___regBuiltinParser_Lean_Parser_Tactic_skip(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__1);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__2);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__3);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__4);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__5);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__6);
l_Lean_Parser_Tactic_traceState___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_traceState___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___elambda__1___closed__7);
l_Lean_Parser_Tactic_traceState___closed__1 = _init_l_Lean_Parser_Tactic_traceState___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___closed__1);
l_Lean_Parser_Tactic_traceState___closed__2 = _init_l_Lean_Parser_Tactic_traceState___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___closed__2);
l_Lean_Parser_Tactic_traceState___closed__3 = _init_l_Lean_Parser_Tactic_traceState___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___closed__3);
l_Lean_Parser_Tactic_traceState___closed__4 = _init_l_Lean_Parser_Tactic_traceState___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___closed__4);
l_Lean_Parser_Tactic_traceState___closed__5 = _init_l_Lean_Parser_Tactic_traceState___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState___closed__5);
l_Lean_Parser_Tactic_traceState = _init_l_Lean_Parser_Tactic_traceState();
lean_mark_persistent(l_Lean_Parser_Tactic_traceState);
res = l___regBuiltinParser_Lean_Parser_Tactic_traceState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_paren___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___elambda__1___closed__1);
l_Lean_Parser_Tactic_paren___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___elambda__1___closed__2);
l_Lean_Parser_Tactic_paren___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___elambda__1___closed__3);
l_Lean_Parser_Tactic_paren___closed__1 = _init_l_Lean_Parser_Tactic_paren___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__1);
l_Lean_Parser_Tactic_paren___closed__2 = _init_l_Lean_Parser_Tactic_paren___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__2);
l_Lean_Parser_Tactic_paren___closed__3 = _init_l_Lean_Parser_Tactic_paren___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__3);
l_Lean_Parser_Tactic_paren___closed__4 = _init_l_Lean_Parser_Tactic_paren___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__4);
l_Lean_Parser_Tactic_paren___closed__5 = _init_l_Lean_Parser_Tactic_paren___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__5);
l_Lean_Parser_Tactic_paren___closed__6 = _init_l_Lean_Parser_Tactic_paren___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_paren___closed__6);
l_Lean_Parser_Tactic_paren = _init_l_Lean_Parser_Tactic_paren();
lean_mark_persistent(l_Lean_Parser_Tactic_paren);
res = l___regBuiltinParser_Lean_Parser_Tactic_paren(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13);
l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__1 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__1);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__2 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__2);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__3 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__3);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__4 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__4);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__5 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__5);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__6 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__6);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__7 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__7);
l_Lean_Parser_Tactic_nestedTacticBlock___closed__8 = _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock___closed__8);
l_Lean_Parser_Tactic_nestedTacticBlock = _init_l_Lean_Parser_Tactic_nestedTacticBlock();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlock);
res = l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5);
l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6 = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6);
l_Lean_Parser_Tactic_nestedTacticBlockCurly = _init_l_Lean_Parser_Tactic_nestedTacticBlockCurly();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTacticBlockCurly);
res = l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_orelse___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___elambda__1___closed__1);
l_Lean_Parser_Tactic_orelse___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___elambda__1___closed__2);
l_Lean_Parser_Tactic_orelse___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___elambda__1___closed__3);
l_Lean_Parser_Tactic_orelse___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___elambda__1___closed__4);
l_Lean_Parser_Tactic_orelse___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_orelse___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___elambda__1___closed__5);
l_Lean_Parser_Tactic_orelse___closed__1 = _init_l_Lean_Parser_Tactic_orelse___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__1);
l_Lean_Parser_Tactic_orelse___closed__2 = _init_l_Lean_Parser_Tactic_orelse___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__2);
l_Lean_Parser_Tactic_orelse___closed__3 = _init_l_Lean_Parser_Tactic_orelse___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__3);
l_Lean_Parser_Tactic_orelse___closed__4 = _init_l_Lean_Parser_Tactic_orelse___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__4);
l_Lean_Parser_Tactic_orelse___closed__5 = _init_l_Lean_Parser_Tactic_orelse___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__5);
l_Lean_Parser_Tactic_orelse___closed__6 = _init_l_Lean_Parser_Tactic_orelse___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__6);
l_Lean_Parser_Tactic_orelse = _init_l_Lean_Parser_Tactic_orelse();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse);
res = l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4);
l_Lean_Parser_Term_tacticBlock___closed__1 = _init_l_Lean_Parser_Term_tacticBlock___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__1);
l_Lean_Parser_Term_tacticBlock___closed__2 = _init_l_Lean_Parser_Term_tacticBlock___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__2);
l_Lean_Parser_Term_tacticBlock___closed__3 = _init_l_Lean_Parser_Term_tacticBlock___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__3);
l_Lean_Parser_Term_tacticBlock___closed__4 = _init_l_Lean_Parser_Term_tacticBlock___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__4);
l_Lean_Parser_Term_tacticBlock___closed__5 = _init_l_Lean_Parser_Term_tacticBlock___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__5);
l_Lean_Parser_Term_tacticBlock___closed__6 = _init_l_Lean_Parser_Term_tacticBlock___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__6);
l_Lean_Parser_Term_tacticBlock = _init_l_Lean_Parser_Term_tacticBlock();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock);
res = l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__1);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__2);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__3);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__4);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__5);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__6);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___closed__7);
l_Lean_Parser_Term_tacticStxQuot___closed__1 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__1);
l_Lean_Parser_Term_tacticStxQuot___closed__2 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__2);
l_Lean_Parser_Term_tacticStxQuot___closed__3 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__3);
l_Lean_Parser_Term_tacticStxQuot___closed__4 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__4);
l_Lean_Parser_Term_tacticStxQuot___closed__5 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__5);
l_Lean_Parser_Term_tacticStxQuot___closed__6 = _init_l_Lean_Parser_Term_tacticStxQuot___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___closed__6);
l_Lean_Parser_Term_tacticStxQuot = _init_l_Lean_Parser_Term_tacticStxQuot();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot);
l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1);
l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2 = _init_l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2();
lean_mark_persistent(l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2);
res = l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
