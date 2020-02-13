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
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_revert___closed__2;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__6;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_apply___closed__2;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_byTactic___closed__4;
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
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_seq;
lean_object* l_Lean_Parser_Tactic_skip___closed__3;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_object*);
extern lean_object* l_Lean_Parser_Term_subst___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_clear___closed__6;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_byTactic;
extern lean_object* l_Lean_Parser_Term_have___closed__3;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_underscore___closed__1;
extern lean_object* l_Lean_Parser_Term_subtype___closed__1;
lean_object* l_Lean_Parser_Tactic_skip___closed__2;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__3;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__7;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__7;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__1;
lean_object* l_Lean_Parser_Tactic_underscore;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__5;
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
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_subst___closed__4;
lean_object* l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse___closed__3;
lean_object* l_Lean_Parser_Tactic_clear___closed__4;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq;
lean_object* l_Lean_Parser_Tactic_revert___closed__1;
lean_object* l_Lean_Parser_Tactic_skip___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___closed__5;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_revert___closed__4;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___closed__4;
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___closed__5;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__6;
lean_object* l_Lean_Parser_Tactic_clear___closed__1;
lean_object* l_Lean_Parser_Tactic_clear___closed__2;
lean_object* l_Lean_Parser_Tactic_clear;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__3;
lean_object* l_Lean_Parser_tacticParser(lean_object*);
lean_object* l_Lean_Parser_Tactic_case___closed__4;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_subst___closed__1;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
lean_object* l_Lean_Parser_Term_tacticStxQuot;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__6;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_assumption;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_subst___closed__2;
lean_object* l_Lean_Parser_Tactic_traceState___closed__5;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__5;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_clear___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_case;
lean_object* l_Lean_Parser_Tactic_traceState___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals;
lean_object* l_Lean_Parser_Tactic_refine___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_case(lean_object*);
lean_object* l_Lean_Parser_Tactic_seq___closed__5;
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__3;
lean_object* l_Lean_Parser_Tactic_subst___closed__6;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__5;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__4;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_seq___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___closed__3;
lean_object* l_Lean_Parser_Tactic_clear___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_revert;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__3;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_revert(lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___closed__2;
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__3;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___closed__2;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_intros___closed__2;
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__2;
lean_object* l_Lean_Parser_Tactic_revert___closed__5;
lean_object* l_Lean_Parser_Tactic_traceState___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___closed__5;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___closed__3;
lean_object* l_Lean_Parser_Tactic_intros___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1;
lean_object* l_Lean_Parser_Tactic_revert___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___elambda__1(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Parser_Term_if___closed__1;
lean_object* l_Lean_Parser_Tactic_ident_x27;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_exact___closed__5;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Parser_Tactic_paren___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__5;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_Tactic_subst___closed__3;
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
lean_object* l_Lean_Parser_Tactic_subst___closed__5;
lean_object* l_Lean_Parser_Tactic_subst;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2;
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__6;
lean_object* l_Lean_Parser_Term_byTactic___closed__5;
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_underscoreFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_refine___closed__1;
lean_object* l_Lean_Parser_Tactic_paren___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_exact(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_clear(lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_allGoals(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__4;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___closed__1;
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___closed__3;
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___closed__5;
lean_object* l_Lean_Parser_Tactic_paren___closed__6;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__3;
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
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__7;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_paren(lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Term_byTactic(lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___closed__3;
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
lean_object* l_Lean_Parser_Term_byTactic___closed__6;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___closed__3;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_orelse___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__5;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_skip(lean_object*);
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_subst(lean_object*);
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
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_traceState(lean_object*);
lean_object* l_Lean_Parser_Term_byTactic___closed__2;
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
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = 1;
x_8 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(x_1, x_5, x_6, x_7, x_2, x_3);
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_5, x_1, x_2);
x_7 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_8 = l_Lean_Parser_ParserState_mkNode(x_6, x_7, x_4);
return x_8;
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
x_4 = l_Lean_Parser_sepByInfo(x_2, x_3);
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
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__1() {
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
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_2 = l_Lean_Parser_Tactic_nonEmptySeq___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nonEmptySeq___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nonEmptySeq___closed__2;
x_2 = l_Lean_Parser_Tactic_nonEmptySeq___closed__3;
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
x_1 = l_Lean_Parser_Tactic_nonEmptySeq___closed__4;
return x_1;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1(x_5, x_6, x_3, x_4);
return x_7;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_10);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_13);
x_19 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_14);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_15, x_23, x_13);
x_25 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Parser_ParserState_restore(x_15, x_13, x_14);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_13);
x_30 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_7);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_1);
x_32 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_10, x_32, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_inc(x_1);
x_37 = lean_apply_2(x_4, x_1, x_2);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_nat_dec_eq(x_40, x_36);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_36);
x_42 = l_Lean_Parser_ParserState_restore(x_37, x_35, x_36);
lean_dec(x_35);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_46 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_1);
x_47 = l_Lean_Parser_nonReservedSymbolFnAux(x_45, x_46, x_1, x_42);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_array_get_size(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
x_52 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_47);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
x_54 = l_Lean_nullKind;
x_55 = l_Lean_Parser_ParserState_mkNode(x_52, x_54, x_50);
x_56 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_57 = l_Lean_Parser_ParserState_mkNode(x_55, x_56, x_44);
x_58 = l_Lean_Parser_mergeOrElseErrors(x_57, x_39, x_36);
lean_dec(x_36);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
x_60 = lean_nat_dec_eq(x_59, x_51);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
x_61 = l_Lean_nullKind;
x_62 = l_Lean_Parser_ParserState_mkNode(x_52, x_61, x_50);
x_63 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_64 = l_Lean_Parser_ParserState_mkNode(x_62, x_63, x_44);
x_65 = l_Lean_Parser_mergeOrElseErrors(x_64, x_39, x_36);
lean_dec(x_36);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_52, x_50, x_51);
x_67 = l_Lean_nullKind;
x_68 = l_Lean_Parser_ParserState_mkNode(x_66, x_67, x_50);
x_69 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_70 = l_Lean_Parser_ParserState_mkNode(x_68, x_69, x_44);
x_71 = l_Lean_Parser_mergeOrElseErrors(x_70, x_39, x_36);
lean_dec(x_36);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_48);
lean_dec(x_1);
x_72 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_73 = l_Lean_Parser_ParserState_mkNode(x_47, x_72, x_44);
x_74 = l_Lean_Parser_mergeOrElseErrors(x_73, x_39, x_36);
lean_dec(x_36);
return x_74;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_10);
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_13);
x_17 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_10, x_19, x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_1);
x_24 = lean_apply_2(x_4, x_1, x_2);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_27, x_23);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_23);
x_29 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_33 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_1);
x_34 = l_Lean_Parser_nonReservedSymbolFnAux(x_32, x_33, x_1, x_29);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_1, x_34);
x_39 = l_Lean_nullKind;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_37);
x_41 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_31);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_26, x_23);
lean_dec(x_23);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_1);
x_44 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_34, x_44, x_31);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_26, x_23);
lean_dec(x_23);
return x_46;
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
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_revert___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_revert___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_revert___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_revert___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_revert___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Parser_ident___elambda__1(x_1, x_10);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_13);
x_19 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_1);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_14, x_21, x_13);
x_23 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_1);
x_25 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_10, x_25, x_7);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_2);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
x_39 = l_Lean_Parser_Tactic_revert___elambda__1___closed__8;
lean_inc(x_1);
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_Parser_ident___elambda__1(x_1, x_40);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_44);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_43);
x_49 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_37);
x_51 = l_Lean_Parser_mergeOrElseErrors(x_50, x_32, x_29);
lean_dec(x_29);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_1);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_44, x_52, x_43);
x_54 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_37);
x_56 = l_Lean_Parser_mergeOrElseErrors(x_55, x_32, x_29);
lean_dec(x_29);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_1);
x_57 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_40, x_57, x_37);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_32, x_29);
lean_dec(x_29);
return x_59;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_revert___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_revert___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_revert___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_revert___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_revert___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_revert___closed__4;
x_2 = l_Lean_Parser_Tactic_revert___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_revert() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_revert___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_revert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_revert;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("clear");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_clear___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_clear___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("clear ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_clear___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_clear___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_clear___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Parser_ident___elambda__1(x_1, x_10);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_13);
x_19 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_1);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_14, x_21, x_13);
x_23 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_1);
x_25 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_10, x_25, x_7);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_2);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
x_39 = l_Lean_Parser_Tactic_clear___elambda__1___closed__8;
lean_inc(x_1);
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_Parser_ident___elambda__1(x_1, x_40);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_44);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_43);
x_49 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_37);
x_51 = l_Lean_Parser_mergeOrElseErrors(x_50, x_32, x_29);
lean_dec(x_29);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_1);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_44, x_52, x_43);
x_54 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_37);
x_56 = l_Lean_Parser_mergeOrElseErrors(x_55, x_32, x_29);
lean_dec(x_29);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_1);
x_57 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_40, x_57, x_37);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_32, x_29);
lean_dec(x_29);
return x_59;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_clear___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_clear___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_clear___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_clear___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_clear___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_clear___closed__4;
x_2 = l_Lean_Parser_Tactic_clear___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_clear() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_clear___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_clear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_clear;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_subst___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_subst___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_subst___elambda__1___closed__2;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__4;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_subst___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_subst___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
x_9 = l_Lean_Parser_Tactic_subst___elambda__1___closed__7;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Parser_ident___elambda__1(x_1, x_10);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_13);
x_19 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_1);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_14, x_21, x_13);
x_23 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_1);
x_25 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkNode(x_10, x_25, x_7);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_apply_2(x_4, x_1, x_2);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_29);
x_35 = l_Lean_Parser_ParserState_restore(x_30, x_28, x_29);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
x_39 = l_Lean_Parser_Tactic_subst___elambda__1___closed__7;
lean_inc(x_1);
x_40 = l_Lean_Parser_nonReservedSymbolFnAux(x_38, x_39, x_1, x_35);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_Parser_ident___elambda__1(x_1, x_40);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_44);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_43);
x_49 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_37);
x_51 = l_Lean_Parser_mergeOrElseErrors(x_50, x_32, x_29);
lean_dec(x_29);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_1);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_44, x_52, x_43);
x_54 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_37);
x_56 = l_Lean_Parser_mergeOrElseErrors(x_55, x_32, x_29);
lean_dec(x_29);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_1);
x_57 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_58 = l_Lean_Parser_ParserState_mkNode(x_40, x_57, x_37);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_32, x_29);
lean_dec(x_29);
return x_59;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_subst___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_subst___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_subst___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_subst___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_subst___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_subst___closed__4;
x_2 = l_Lean_Parser_Tactic_subst___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_subst() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_subst___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_subst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_subst;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_9 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_apply_2(x_4, x_1, x_2);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_19, x_15);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_15);
x_21 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_25 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_26 = l_Lean_Parser_nonReservedSymbolFnAux(x_24, x_25, x_1, x_21);
x_27 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_23);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_18, x_15);
lean_dec(x_15);
return x_29;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_apply___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_termParser___closed__2;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_categoryParser___elambda__1(x_12, x_13, x_1, x_10);
x_15 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_1);
x_17 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_10, x_17, x_7);
return x_18;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_21);
x_27 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_31 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_1);
x_32 = l_Lean_Parser_nonReservedSymbolFnAux(x_30, x_31, x_1, x_27);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Parser_termParser___closed__2;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Parser_categoryParser___elambda__1(x_34, x_35, x_1, x_32);
x_37 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_29);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_24, x_21);
lean_dec(x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_1);
x_40 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_32, x_40, x_29);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_24, x_21);
lean_dec(x_21);
return x_42;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_termParser___closed__2;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_categoryParser___elambda__1(x_12, x_13, x_1, x_10);
x_15 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_1);
x_17 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_10, x_17, x_7);
return x_18;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_21);
x_27 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
x_31 = l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
lean_inc(x_1);
x_32 = l_Lean_Parser_nonReservedSymbolFnAux(x_30, x_31, x_1, x_27);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Parser_termParser___closed__2;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Parser_categoryParser___elambda__1(x_34, x_35, x_1, x_32);
x_37 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_29);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_24, x_21);
lean_dec(x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_1);
x_40 = l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_32, x_40, x_29);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_24, x_21);
lean_dec(x_21);
return x_42;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_refine___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_termParser___closed__2;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_categoryParser___elambda__1(x_12, x_13, x_1, x_10);
x_15 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_1);
x_17 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_10, x_17, x_7);
return x_18;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_21);
x_27 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
x_31 = l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_inc(x_1);
x_32 = l_Lean_Parser_nonReservedSymbolFnAux(x_30, x_31, x_1, x_27);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Parser_termParser___closed__2;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Parser_categoryParser___elambda__1(x_34, x_35, x_1, x_32);
x_37 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_29);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_24, x_21);
lean_dec(x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_1);
x_40 = l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_32, x_40, x_29);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_24, x_21);
lean_dec(x_21);
return x_42;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_case___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_9 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_ident___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_1);
x_21 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_10, x_21, x_7);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_1);
x_26 = lean_apply_2(x_4, x_1, x_2);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_nat_dec_eq(x_29, x_25);
lean_dec(x_29);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_25);
x_31 = l_Lean_Parser_ParserState_restore(x_26, x_24, x_25);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_array_get_size(x_32);
lean_dec(x_32);
x_34 = l_Lean_Parser_Tactic_case___elambda__1___closed__5;
x_35 = l_Lean_Parser_Tactic_case___elambda__1___closed__7;
lean_inc(x_1);
x_36 = l_Lean_Parser_nonReservedSymbolFnAux(x_34, x_35, x_1, x_31);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_1);
x_38 = l_Lean_Parser_ident___elambda__1(x_1, x_36);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Parser_categoryParser___elambda__1(x_40, x_41, x_1, x_38);
x_43 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_44 = l_Lean_Parser_ParserState_mkNode(x_42, x_43, x_33);
x_45 = l_Lean_Parser_mergeOrElseErrors(x_44, x_28, x_25);
lean_dec(x_25);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_1);
x_46 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_47 = l_Lean_Parser_ParserState_mkNode(x_38, x_46, x_33);
x_48 = l_Lean_Parser_mergeOrElseErrors(x_47, x_28, x_25);
lean_dec(x_25);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_1);
x_49 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_36, x_49, x_33);
x_51 = l_Lean_Parser_mergeOrElseErrors(x_50, x_28, x_25);
lean_dec(x_25);
return x_51;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_categoryParser___elambda__1(x_12, x_13, x_1, x_10);
x_15 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_1);
x_17 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_10, x_17, x_7);
return x_18;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_21);
x_27 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
x_31 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
lean_inc(x_1);
x_32 = l_Lean_Parser_nonReservedSymbolFnAux(x_30, x_31, x_1, x_27);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Parser_categoryParser___elambda__1(x_34, x_35, x_1, x_32);
x_37 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_29);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_24, x_21);
lean_dec(x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_1);
x_40 = l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_32, x_40, x_29);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_24, x_21);
lean_dec(x_21);
return x_42;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_9 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_apply_2(x_4, x_1, x_2);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_19, x_15);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_15);
x_21 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
x_25 = l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
x_26 = l_Lean_Parser_nonReservedSymbolFnAux(x_24, x_25, x_1, x_21);
x_27 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_23);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_18, x_15);
lean_dec(x_15);
return x_29;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_9 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_apply_2(x_4, x_1, x_2);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_19, x_15);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_15);
x_21 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_15);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
x_25 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
x_26 = l_Lean_Parser_nonReservedSymbolFnAux(x_24, x_25, x_1, x_21);
x_27 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_23);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_18, x_15);
lean_dec(x_15);
return x_29;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_paren___elambda__1___closed__3;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_1);
x_40 = l_Lean_Parser_tokenFn(x_1, x_2);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 2)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_47, x_39);
x_8 = x_48;
goto block_38;
}
else
{
lean_dec(x_39);
x_8 = x_40;
goto block_38;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_51, x_39);
x_8 = x_52;
goto block_38;
}
block_38:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_tokenFn(x_1, x_10);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_20, x_12);
x_22 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_13, x_24, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_26 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_26, x_12);
x_28 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_30 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_30, x_12);
x_32 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_1);
x_34 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_35 = l_Lean_Parser_ParserState_mkNode(x_10, x_34, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_37 = l_Lean_Parser_ParserState_mkNode(x_8, x_36, x_7);
return x_37;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_apply_2(x_4, x_1, x_2);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_nat_dec_eq(x_59, x_55);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_101; lean_object* x_102; 
lean_inc(x_55);
x_61 = l_Lean_Parser_ParserState_restore(x_56, x_54, x_55);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
lean_inc(x_1);
x_101 = l_Lean_Parser_tokenFn(x_1, x_61);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 2)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__3;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_55);
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_108, x_55);
x_64 = x_109;
goto block_100;
}
else
{
x_64 = x_101;
goto block_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_110 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_55);
x_111 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_110, x_55);
x_64 = x_111;
goto block_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
x_112 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__10;
lean_inc(x_55);
x_113 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_112, x_55);
x_64 = x_113;
goto block_100;
}
block_100:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_1);
x_66 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_64);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = l_Lean_Parser_tokenFn(x_1, x_66);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 2)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__4;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_77 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_76, x_68);
x_78 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_63);
x_80 = l_Lean_Parser_mergeOrElseErrors(x_79, x_58, x_55);
lean_dec(x_55);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_81 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_82 = l_Lean_Parser_ParserState_mkNode(x_69, x_81, x_63);
x_83 = l_Lean_Parser_mergeOrElseErrors(x_82, x_58, x_55);
lean_dec(x_55);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
x_84 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_84, x_68);
x_86 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_63);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_58, x_55);
lean_dec(x_55);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_70);
x_89 = l___private_Init_Lean_Parser_Parser_12__antiquotNestedExpr___elambda__1___closed__7;
x_90 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_89, x_68);
x_91 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_63);
x_93 = l_Lean_Parser_mergeOrElseErrors(x_92, x_58, x_55);
lean_dec(x_55);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_67);
lean_dec(x_1);
x_94 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_95 = l_Lean_Parser_ParserState_mkNode(x_66, x_94, x_63);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_58, x_55);
lean_dec(x_55);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_65);
lean_dec(x_1);
x_97 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_98 = l_Lean_Parser_ParserState_mkNode(x_64, x_97, x_63);
x_99 = l_Lean_Parser_mergeOrElseErrors(x_98, x_58, x_55);
lean_dec(x_55);
return x_99;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_1);
x_40 = l_Lean_Parser_tokenFn(x_1, x_2);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 2)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_47, x_39);
x_8 = x_48;
goto block_38;
}
else
{
lean_dec(x_39);
x_8 = x_40;
goto block_38;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_51, x_39);
x_8 = x_52;
goto block_38;
}
block_38:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_tokenFn(x_1, x_10);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_20, x_12);
x_22 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_13, x_24, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_26 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_26, x_12);
x_28 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_30 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_30, x_12);
x_32 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_1);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_10, x_34, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_8, x_36, x_7);
return x_37;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_apply_2(x_4, x_1, x_2);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_nat_dec_eq(x_59, x_55);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_101; lean_object* x_102; 
lean_inc(x_55);
x_61 = l_Lean_Parser_ParserState_restore(x_56, x_54, x_55);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
lean_inc(x_1);
x_101 = l_Lean_Parser_tokenFn(x_1, x_61);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 2)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_108, x_55);
x_64 = x_109;
goto block_100;
}
else
{
x_64 = x_101;
goto block_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_110 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_111 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_110, x_55);
x_64 = x_111;
goto block_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
x_112 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_113 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_112, x_55);
x_64 = x_113;
goto block_100;
}
block_100:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_1);
x_66 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_64);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = l_Lean_Parser_tokenFn(x_1, x_66);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 2)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_77 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_76, x_68);
x_78 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_63);
x_80 = l_Lean_Parser_mergeOrElseErrors(x_79, x_58, x_55);
lean_dec(x_55);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_81 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_82 = l_Lean_Parser_ParserState_mkNode(x_69, x_81, x_63);
x_83 = l_Lean_Parser_mergeOrElseErrors(x_82, x_58, x_55);
lean_dec(x_55);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
x_84 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_84, x_68);
x_86 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_63);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_58, x_55);
lean_dec(x_55);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_70);
x_89 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_90 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_89, x_68);
x_91 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_63);
x_93 = l_Lean_Parser_mergeOrElseErrors(x_92, x_58, x_55);
lean_dec(x_55);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_67);
lean_dec(x_1);
x_94 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_95 = l_Lean_Parser_ParserState_mkNode(x_66, x_94, x_63);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_58, x_55);
lean_dec(x_55);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_65);
lean_dec(x_1);
x_97 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_98 = l_Lean_Parser_ParserState_mkNode(x_64, x_97, x_63);
x_99 = l_Lean_Parser_mergeOrElseErrors(x_98, x_58, x_55);
lean_dec(x_55);
return x_99;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_1);
x_40 = l_Lean_Parser_tokenFn(x_1, x_2);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 2)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_47, x_39);
x_8 = x_48;
goto block_38;
}
else
{
lean_dec(x_39);
x_8 = x_40;
goto block_38;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_51, x_39);
x_8 = x_52;
goto block_38;
}
block_38:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_tokenFn(x_1, x_10);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_20, x_12);
x_22 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_13, x_24, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_26 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_26, x_12);
x_28 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_30 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_30, x_12);
x_32 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_1);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_10, x_34, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_1);
x_36 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_8, x_36, x_7);
return x_37;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_apply_2(x_4, x_1, x_2);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_nat_dec_eq(x_59, x_55);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_101; lean_object* x_102; 
lean_inc(x_55);
x_61 = l_Lean_Parser_ParserState_restore(x_56, x_54, x_55);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
lean_inc(x_1);
x_101 = l_Lean_Parser_tokenFn(x_1, x_61);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 2)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_55);
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_108, x_55);
x_64 = x_109;
goto block_100;
}
else
{
x_64 = x_101;
goto block_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_110 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_55);
x_111 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_110, x_55);
x_64 = x_111;
goto block_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
x_112 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_55);
x_113 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_112, x_55);
x_64 = x_113;
goto block_100;
}
block_100:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_1);
x_66 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_64);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = l_Lean_Parser_tokenFn(x_1, x_66);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 2)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_77 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_76, x_68);
x_78 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_63);
x_80 = l_Lean_Parser_mergeOrElseErrors(x_79, x_58, x_55);
lean_dec(x_55);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_81 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_82 = l_Lean_Parser_ParserState_mkNode(x_69, x_81, x_63);
x_83 = l_Lean_Parser_mergeOrElseErrors(x_82, x_58, x_55);
lean_dec(x_55);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
x_84 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_84, x_68);
x_86 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_63);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_58, x_55);
lean_dec(x_55);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_70);
x_89 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
x_90 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_89, x_68);
x_91 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_63);
x_93 = l_Lean_Parser_mergeOrElseErrors(x_92, x_58, x_55);
lean_dec(x_55);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_67);
lean_dec(x_1);
x_94 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_95 = l_Lean_Parser_ParserState_mkNode(x_66, x_94, x_63);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_58, x_55);
lean_dec(x_55);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_65);
lean_dec(x_1);
x_97 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_98 = l_Lean_Parser_ParserState_mkNode(x_64, x_97, x_63);
x_99 = l_Lean_Parser_mergeOrElseErrors(x_98, x_58, x_55);
lean_dec(x_55);
return x_99;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_1);
x_40 = l_Lean_Parser_tokenFn(x_1, x_2);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 2)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_47, x_39);
x_8 = x_48;
goto block_38;
}
else
{
lean_dec(x_39);
x_8 = x_40;
goto block_38;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
x_52 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_51, x_39);
x_8 = x_52;
goto block_38;
}
block_38:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_tokenFn(x_1, x_10);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_20, x_12);
x_22 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_24 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_13, x_24, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_26 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_26, x_12);
x_28 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_30 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_31 = l_Lean_Parser_ParserState_mkErrorsAt(x_13, x_30, x_12);
x_32 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_1);
x_34 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_10, x_34, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_1);
x_36 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_8, x_36, x_7);
return x_37;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_apply_2(x_4, x_1, x_2);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_nat_dec_eq(x_59, x_55);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_101; lean_object* x_102; 
lean_inc(x_55);
x_61 = l_Lean_Parser_ParserState_restore(x_56, x_54, x_55);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
lean_inc(x_1);
x_101 = l_Lean_Parser_tokenFn(x_1, x_61);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 2)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_108, x_55);
x_64 = x_109;
goto block_100;
}
else
{
x_64 = x_101;
goto block_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_110 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_111 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_110, x_55);
x_64 = x_111;
goto block_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
x_112 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_55);
x_113 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_112, x_55);
x_64 = x_113;
goto block_100;
}
block_100:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_1);
x_66 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_64);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = l_Lean_Parser_tokenFn(x_1, x_66);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 2)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_77 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_76, x_68);
x_78 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_63);
x_80 = l_Lean_Parser_mergeOrElseErrors(x_79, x_58, x_55);
lean_dec(x_55);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_81 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_82 = l_Lean_Parser_ParserState_mkNode(x_69, x_81, x_63);
x_83 = l_Lean_Parser_mergeOrElseErrors(x_82, x_58, x_55);
lean_dec(x_55);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
x_84 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_84, x_68);
x_86 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_63);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_58, x_55);
lean_dec(x_55);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_70);
x_89 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_90 = l_Lean_Parser_ParserState_mkErrorsAt(x_69, x_89, x_68);
x_91 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_63);
x_93 = l_Lean_Parser_mergeOrElseErrors(x_92, x_58, x_55);
lean_dec(x_55);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_67);
lean_dec(x_1);
x_94 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_95 = l_Lean_Parser_ParserState_mkNode(x_66, x_94, x_63);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_58, x_55);
lean_dec(x_55);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_65);
lean_dec(x_1);
x_97 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_98 = l_Lean_Parser_ParserState_mkNode(x_64, x_97, x_63);
x_99 = l_Lean_Parser_mergeOrElseErrors(x_98, x_58, x_55);
lean_dec(x_55);
return x_99;
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
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("byTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Parser_Term_byTactic___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__1;
x_2 = l_Lean_Parser_Term_byTactic___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_byTactic___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_byTactic___elambda__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_byTactic___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Term_byTactic___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l_Lean_Parser_tokenFn(x_1, x_2);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Parser_Term_byTactic___elambda__1___closed__6;
x_23 = lean_string_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_24, x_16);
x_8 = x_25;
goto block_15;
}
else
{
lean_dec(x_16);
x_8 = x_17;
goto block_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_26 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_26, x_16);
x_8 = x_27;
goto block_15;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
x_28 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_28, x_16);
x_8 = x_29;
goto block_15;
}
block_15:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_8);
x_11 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_8, x_13, x_7);
return x_14;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_1);
x_33 = lean_apply_2(x_4, x_1, x_2);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_nat_dec_eq(x_36, x_32);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; lean_object* x_52; 
lean_inc(x_32);
x_38 = l_Lean_Parser_ParserState_restore(x_33, x_31, x_32);
lean_dec(x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
lean_inc(x_1);
x_51 = l_Lean_Parser_tokenFn(x_1, x_38);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 2)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Parser_Term_byTactic___elambda__1___closed__6;
x_57 = lean_string_dec_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
lean_inc(x_32);
x_59 = l_Lean_Parser_ParserState_mkErrorsAt(x_51, x_58, x_32);
x_41 = x_59;
goto block_50;
}
else
{
x_41 = x_51;
goto block_50;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_54);
x_60 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
lean_inc(x_32);
x_61 = l_Lean_Parser_ParserState_mkErrorsAt(x_51, x_60, x_32);
x_41 = x_61;
goto block_50;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_52);
x_62 = l_Lean_Parser_Term_byTactic___elambda__1___closed__9;
lean_inc(x_32);
x_63 = l_Lean_Parser_ParserState_mkErrorsAt(x_51, x_62, x_32);
x_41 = x_63;
goto block_50;
}
block_50:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(x_1, x_41);
x_44 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_40);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_35, x_32);
lean_dec(x_32);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_1);
x_47 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_41, x_47, x_40);
x_49 = l_Lean_Parser_mergeOrElseErrors(x_48, x_35, x_32);
lean_dec(x_32);
return x_49;
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__6;
x_2 = l_Lean_Parser_Term_if___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nonEmptySeq;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_byTactic___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_byTactic___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_byTactic___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_byTactic___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_byTactic___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_byTactic___closed__4;
x_2 = l_Lean_Parser_Term_byTactic___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_byTactic() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_byTactic___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_byTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_termParser___closed__2;
x_3 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Term_byTactic;
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
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_nonEmptySeq___elambda__1___spec__1(x_7, x_7, x_1, x_5);
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
x_1 = l_Lean_Parser_Tactic_nonEmptySeq___closed__1;
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
l_Lean_Parser_Tactic_nonEmptySeq___closed__3 = _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_nonEmptySeq___closed__3);
l_Lean_Parser_Tactic_nonEmptySeq___closed__4 = _init_l_Lean_Parser_Tactic_nonEmptySeq___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_nonEmptySeq___closed__4);
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
l_Lean_Parser_Tactic_revert___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__1);
l_Lean_Parser_Tactic_revert___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__2);
l_Lean_Parser_Tactic_revert___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__3);
l_Lean_Parser_Tactic_revert___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__4);
l_Lean_Parser_Tactic_revert___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__5);
l_Lean_Parser_Tactic_revert___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__6);
l_Lean_Parser_Tactic_revert___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__7);
l_Lean_Parser_Tactic_revert___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_revert___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___elambda__1___closed__8);
l_Lean_Parser_Tactic_revert___closed__1 = _init_l_Lean_Parser_Tactic_revert___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__1);
l_Lean_Parser_Tactic_revert___closed__2 = _init_l_Lean_Parser_Tactic_revert___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__2);
l_Lean_Parser_Tactic_revert___closed__3 = _init_l_Lean_Parser_Tactic_revert___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__3);
l_Lean_Parser_Tactic_revert___closed__4 = _init_l_Lean_Parser_Tactic_revert___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__4);
l_Lean_Parser_Tactic_revert___closed__5 = _init_l_Lean_Parser_Tactic_revert___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__5);
l_Lean_Parser_Tactic_revert___closed__6 = _init_l_Lean_Parser_Tactic_revert___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_revert___closed__6);
l_Lean_Parser_Tactic_revert = _init_l_Lean_Parser_Tactic_revert();
lean_mark_persistent(l_Lean_Parser_Tactic_revert);
res = l___regBuiltinParser_Lean_Parser_Tactic_revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_clear___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__1);
l_Lean_Parser_Tactic_clear___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__2);
l_Lean_Parser_Tactic_clear___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__3);
l_Lean_Parser_Tactic_clear___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__4);
l_Lean_Parser_Tactic_clear___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__5);
l_Lean_Parser_Tactic_clear___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__6);
l_Lean_Parser_Tactic_clear___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__7);
l_Lean_Parser_Tactic_clear___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_clear___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___elambda__1___closed__8);
l_Lean_Parser_Tactic_clear___closed__1 = _init_l_Lean_Parser_Tactic_clear___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__1);
l_Lean_Parser_Tactic_clear___closed__2 = _init_l_Lean_Parser_Tactic_clear___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__2);
l_Lean_Parser_Tactic_clear___closed__3 = _init_l_Lean_Parser_Tactic_clear___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__3);
l_Lean_Parser_Tactic_clear___closed__4 = _init_l_Lean_Parser_Tactic_clear___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__4);
l_Lean_Parser_Tactic_clear___closed__5 = _init_l_Lean_Parser_Tactic_clear___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__5);
l_Lean_Parser_Tactic_clear___closed__6 = _init_l_Lean_Parser_Tactic_clear___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_clear___closed__6);
l_Lean_Parser_Tactic_clear = _init_l_Lean_Parser_Tactic_clear();
lean_mark_persistent(l_Lean_Parser_Tactic_clear);
res = l___regBuiltinParser_Lean_Parser_Tactic_clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_subst___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__1);
l_Lean_Parser_Tactic_subst___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__2);
l_Lean_Parser_Tactic_subst___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__3);
l_Lean_Parser_Tactic_subst___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__4);
l_Lean_Parser_Tactic_subst___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__5);
l_Lean_Parser_Tactic_subst___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__6);
l_Lean_Parser_Tactic_subst___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_subst___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___elambda__1___closed__7);
l_Lean_Parser_Tactic_subst___closed__1 = _init_l_Lean_Parser_Tactic_subst___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__1);
l_Lean_Parser_Tactic_subst___closed__2 = _init_l_Lean_Parser_Tactic_subst___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__2);
l_Lean_Parser_Tactic_subst___closed__3 = _init_l_Lean_Parser_Tactic_subst___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__3);
l_Lean_Parser_Tactic_subst___closed__4 = _init_l_Lean_Parser_Tactic_subst___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__4);
l_Lean_Parser_Tactic_subst___closed__5 = _init_l_Lean_Parser_Tactic_subst___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__5);
l_Lean_Parser_Tactic_subst___closed__6 = _init_l_Lean_Parser_Tactic_subst___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_subst___closed__6);
l_Lean_Parser_Tactic_subst = _init_l_Lean_Parser_Tactic_subst();
lean_mark_persistent(l_Lean_Parser_Tactic_subst);
res = l___regBuiltinParser_Lean_Parser_Tactic_subst(lean_io_mk_world());
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
l_Lean_Parser_Term_byTactic___elambda__1___closed__1 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__1);
l_Lean_Parser_Term_byTactic___elambda__1___closed__2 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__2);
l_Lean_Parser_Term_byTactic___elambda__1___closed__3 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__3);
l_Lean_Parser_Term_byTactic___elambda__1___closed__4 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__4);
l_Lean_Parser_Term_byTactic___elambda__1___closed__5 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__5);
l_Lean_Parser_Term_byTactic___elambda__1___closed__6 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__6);
l_Lean_Parser_Term_byTactic___elambda__1___closed__7 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__7);
l_Lean_Parser_Term_byTactic___elambda__1___closed__8 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__8);
l_Lean_Parser_Term_byTactic___elambda__1___closed__9 = _init_l_Lean_Parser_Term_byTactic___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___elambda__1___closed__9);
l_Lean_Parser_Term_byTactic___closed__1 = _init_l_Lean_Parser_Term_byTactic___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__1);
l_Lean_Parser_Term_byTactic___closed__2 = _init_l_Lean_Parser_Term_byTactic___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__2);
l_Lean_Parser_Term_byTactic___closed__3 = _init_l_Lean_Parser_Term_byTactic___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__3);
l_Lean_Parser_Term_byTactic___closed__4 = _init_l_Lean_Parser_Term_byTactic___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__4);
l_Lean_Parser_Term_byTactic___closed__5 = _init_l_Lean_Parser_Term_byTactic___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__5);
l_Lean_Parser_Term_byTactic___closed__6 = _init_l_Lean_Parser_Term_byTactic___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_byTactic___closed__6);
l_Lean_Parser_Term_byTactic = _init_l_Lean_Parser_Term_byTactic();
lean_mark_persistent(l_Lean_Parser_Term_byTactic);
res = l___regBuiltinParser_Lean_Parser_Term_byTactic(lean_io_mk_world());
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
