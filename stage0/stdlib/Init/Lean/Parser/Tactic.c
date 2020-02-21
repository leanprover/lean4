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
lean_object* l_Lean_Parser_Tactic_withAlts___closed__2;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___closed__6;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_induction___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_revert___closed__2;
lean_object* l_Lean_Parser_Tactic_case___closed__6;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__2;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__5;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_orelse___closed__1;
lean_object* l_Lean_Parser_Tactic_underscore___closed__2;
lean_object* l_Lean_Parser_Tactic_majorPremise___closed__4;
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_majorPremise___closed__1;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_Tactic_seq;
lean_object* l_Lean_Parser_Tactic_skip___closed__3;
lean_object* l_Lean_Parser_Tactic_induction___closed__2;
lean_object* l_Lean_Parser_Tactic_generalizingVars___closed__5;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_Term_tacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__8;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_object*);
lean_object* l_Lean_Parser_Tactic_withAlts___closed__4;
extern lean_object* l_Lean_Parser_Term_subst___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_withAlts___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_clear___closed__6;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__11(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_inductionAlts;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_underscore___closed__1;
lean_object* l_Lean_Parser_Tactic_usingRec___closed__2;
extern lean_object* l_Lean_Parser_Term_subtype___closed__1;
lean_object* l_Lean_Parser_Tactic_skip___closed__2;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__4;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__4;
lean_object* l_Lean_Parser_Tactic_inductionAlt;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_usingRec___closed__1;
lean_object* l_Lean_Parser_Tactic_underscore;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__4;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__7;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_paren___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__5;
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___closed__1;
lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__7;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___closed__4;
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2;
lean_object* l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_usingRec;
lean_object* l_Lean_Parser_Tactic_orelse___closed__3;
lean_object* l_Lean_Parser_Tactic_clear___closed__4;
extern lean_object* l_Lean_Parser_Tactic_nonEmptySeq;
lean_object* l_Lean_Parser_Tactic_revert___closed__1;
lean_object* l_Lean_Parser_Tactic_skip___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__5;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___closed__5;
extern lean_object* l_Lean_Parser_Term_optIdent___closed__2;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_revert___closed__4;
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_usingRec___closed__4;
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
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__14;
lean_object* l_Lean_Parser_Tactic_case___closed__4;
lean_object* l_Lean_Parser_Tactic_subst___closed__1;
lean_object* l_Lean_Parser_Tactic_induction;
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_usingRec___closed__5;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__5;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___closed__2;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_inductionAlts___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___closed__5;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__10;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_clear___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case;
lean_object* l_Lean_Parser_Tactic_traceState___closed__1;
extern lean_object* l_Lean_Parser_ident___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals;
lean_object* l_Lean_Parser_Tactic_refine___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_case(lean_object*);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__3;
lean_object* l_Lean_Parser_Tactic_subst___closed__6;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__5;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___closed__3;
lean_object* l_Lean_Parser_Tactic_clear___closed__5;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__3;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_usingRec___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_revert(lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object*);
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__3;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_intros___closed__2;
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__7;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_Tactic_induction___closed__7;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___closed__5;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_traceState___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___closed__5;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_object*);
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_apply___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___closed__3;
lean_object* l_Lean_Parser_Tactic_intros___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__5;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__12;
lean_object* l_Lean_Parser_Tactic_revert___closed__6;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_majorPremise___closed__3;
extern lean_object* l_Lean_Parser_termParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___closed__2;
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__6;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_majorPremise___closed__5;
lean_object* l_Lean_Parser_Tactic_exact___closed__3;
lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__3;
lean_object* l_Lean_Parser_Tactic_paren___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___closed__2;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__8;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_ident_x27;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_exact___closed__5;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_paren___closed__3;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__3;
lean_object* l_Lean_Parser_Tactic_majorPremise___closed__2;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_generalizingVars___closed__4;
lean_object* l_Lean_Parser_Tactic_intro___closed__7;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock;
extern lean_object* l_Lean_Parser_Term_explicitUniv___closed__4;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__6;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_allGoals___closed__2;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply;
lean_object* l_Lean_Parser_Tactic_assumption___closed__5;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_paren___closed__1;
lean_object* l_Lean_Parser_Tactic_paren___closed__2;
lean_object* l_Lean_Parser_Tactic_subst___closed__3;
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_case___closed__5;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__6;
lean_object* l_Lean_Parser_Tactic_subst___closed__5;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_object* l_Lean_Parser_Tactic_subst;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__4;
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__6;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_underscoreFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_refine___closed__1;
lean_object* l_Lean_Parser_Tactic_paren___closed__4;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_exact(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___closed__3;
lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_clear(lean_object*);
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_allGoals(lean_object*);
lean_object* l_Lean_Parser_Tactic_induction___closed__6;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_withAlts___elambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_withAlts;
lean_object* l_Lean_Parser_Tactic_refine___closed__4;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___closed__1;
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__5;
lean_object* l_Lean_Parser_Tactic_paren___closed__6;
lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_generalizingVars___closed__1;
lean_object* l_Lean_Parser_Tactic_generalizingVars;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__9;
lean_object* l_Lean_Parser_Tactic_induction___closed__3;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4;
lean_object* l_Lean_Parser_Tactic_assumption___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__7;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4;
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_generalizingVars___closed__2;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_induction___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__2;
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__6;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___closed__6;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__9(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_intros;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5;
lean_object* l_Lean_Parser_Tactic_case___closed__7;
lean_object* l_Lean_Parser_Tactic_exact___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_paren(lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__2;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Tactic_nonEmptySeq___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_object*);
extern lean_object* l_Lean_Parser_Term_matchAlts___closed__1;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__2;
lean_object* l_Lean_Parser_Tactic_induction___closed__4;
extern lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__2;
lean_object* l_Lean_Parser_Tactic_induction___closed__8;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__1;
lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Tactic_seq___closed__1;
lean_object* l_Lean_Parser_Tactic_exact___closed__2;
lean_object* l_Lean_Parser_Tactic_intro___closed__2;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__5;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__1;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__3;
lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_induction(lean_object*);
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_induction___closed__9;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__4;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__4;
lean_object* l_Lean_Parser_Tactic_generalizingVars___closed__3;
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_Term_fun___closed__2;
lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__1;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___closed__3;
extern lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__5;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_exact___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_skip(lean_object*);
lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__6;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_subst(lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_skip;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_refine___elambda__1___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object*);
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_allGoals___closed__1;
lean_object* l_Lean_Parser_Tactic_traceState;
lean_object* l_Lean_Parser_Tactic_subst___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_traceState(lean_object*);
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_paren;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro;
extern lean_object* l_Lean_Parser_Parser_inhabited___closed__1;
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_refine;
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__3;
extern lean_object* l_Lean_ppGoal___closed__7;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__8;
extern lean_object* l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__2;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_refine(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_skip___closed__4;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__4;
lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_traceState___elambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
lean_object* l_Lean_Parser_Tactic_allGoals___elambda__1___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_withAlts___closed__3;
lean_object* l_Lean_Parser_Tactic_majorPremise;
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__2;
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
x_1 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__2;
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
x_1 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__2;
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
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("majorPremise");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_majorPremise___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Parser_tryAnti(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
lean_dec(x_6);
lean_inc(x_1);
x_52 = l_Lean_Parser_ident___elambda__1(x_1, x_2);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_inc(x_1);
x_55 = l_Lean_Parser_tokenFn(x_1, x_52);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 2)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__5;
x_61 = lean_string_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_63 = l_Lean_Parser_ParserState_mkErrorsAt(x_55, x_62, x_54);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 3);
lean_inc(x_66);
x_45 = x_63;
x_46 = x_64;
x_47 = x_65;
x_48 = x_66;
goto block_51;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 3);
lean_inc(x_69);
x_45 = x_55;
x_46 = x_67;
x_47 = x_68;
x_48 = x_69;
goto block_51;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_58);
x_70 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_71 = l_Lean_Parser_ParserState_mkErrorsAt(x_55, x_70, x_54);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_45 = x_71;
x_46 = x_72;
x_47 = x_73;
x_48 = x_74;
goto block_51;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_56);
x_75 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_76 = l_Lean_Parser_ParserState_mkErrorsAt(x_55, x_75, x_54);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 3);
lean_inc(x_79);
x_45 = x_76;
x_46 = x_77;
x_47 = x_78;
x_48 = x_79;
goto block_51;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_53);
x_80 = lean_ctor_get(x_52, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_52, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_52, 3);
lean_inc(x_82);
x_45 = x_52;
x_46 = x_80;
x_47 = x_81;
x_48 = x_82;
goto block_51;
}
block_44:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_11 = l_Lean_nullKind;
lean_inc(x_8);
x_12 = l_Lean_Parser_ParserState_mkNode(x_9, x_11, x_8);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Parser_termParser___closed__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_categoryParser___elambda__1(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_8);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_7);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_23 = l_Lean_nullKind;
lean_inc(x_8);
x_24 = l_Lean_Parser_ParserState_mkNode(x_9, x_23, x_8);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_Parser_termParser___closed__2;
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Parser_categoryParser___elambda__1(x_26, x_27, x_1, x_24);
x_29 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_1);
x_31 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_24, x_31, x_8);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lean_Parser_ParserState_restore(x_9, x_8, x_7);
x_34 = l_Lean_nullKind;
lean_inc(x_8);
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_8);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Lean_Parser_termParser___closed__2;
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Parser_categoryParser___elambda__1(x_37, x_38, x_1, x_35);
x_40 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_8);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_1);
x_42 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_43 = l_Lean_Parser_ParserState_mkNode(x_35, x_42, x_8);
return x_43;
}
}
}
}
block_51:
{
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_47);
lean_dec(x_46);
x_9 = x_45;
goto block_44;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_49 = l_Array_shrink___main___rarg(x_46, x_8);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_7);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
x_9 = x_50;
goto block_44;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
x_85 = lean_array_get_size(x_83);
lean_dec(x_83);
lean_inc(x_2);
lean_inc(x_1);
x_86 = lean_apply_2(x_4, x_1, x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_87 = x_2;
} else {
 lean_dec_ref(x_2);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_86, 3);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_1);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
x_91 = lean_nat_dec_eq(x_90, x_84);
lean_dec(x_90);
if (x_91 == 0)
{
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_1);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_144; lean_object* x_145; 
lean_inc(x_84);
x_92 = l_Lean_Parser_ParserState_restore(x_86, x_85, x_84);
lean_dec(x_85);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_array_get_size(x_93);
lean_dec(x_93);
lean_inc(x_1);
x_144 = l_Lean_Parser_ident___elambda__1(x_1, x_92);
x_145 = lean_ctor_get(x_144, 3);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_inc(x_1);
x_147 = l_Lean_Parser_tokenFn(x_1, x_144);
x_148 = lean_ctor_get(x_147, 3);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_149);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 2)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__5;
x_153 = lean_string_dec_eq(x_151, x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_155 = l_Lean_Parser_ParserState_mkErrorsAt(x_147, x_154, x_146);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 3);
lean_inc(x_158);
x_137 = x_155;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
goto block_143;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_146);
x_159 = lean_ctor_get(x_147, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_147, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_147, 3);
lean_inc(x_161);
x_137 = x_147;
x_138 = x_159;
x_139 = x_160;
x_140 = x_161;
goto block_143;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_150);
x_162 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_163 = l_Lean_Parser_ParserState_mkErrorsAt(x_147, x_162, x_146);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 3);
lean_inc(x_166);
x_137 = x_163;
x_138 = x_164;
x_139 = x_165;
x_140 = x_166;
goto block_143;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_148);
x_167 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__8;
x_168 = l_Lean_Parser_ParserState_mkErrorsAt(x_147, x_167, x_146);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 3);
lean_inc(x_171);
x_137 = x_168;
x_138 = x_169;
x_139 = x_170;
x_140 = x_171;
goto block_143;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_145);
x_172 = lean_ctor_get(x_144, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_144, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_144, 3);
lean_inc(x_174);
x_137 = x_144;
x_138 = x_172;
x_139 = x_173;
x_140 = x_174;
goto block_143;
}
block_136:
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 3);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = l_Lean_nullKind;
lean_inc(x_94);
x_98 = l_Lean_Parser_ParserState_mkNode(x_95, x_97, x_94);
x_99 = lean_ctor_get(x_98, 3);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = l_Lean_Parser_termParser___closed__2;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_Parser_categoryParser___elambda__1(x_100, x_101, x_1, x_98);
x_103 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_104 = l_Lean_Parser_ParserState_mkNode(x_102, x_103, x_94);
x_105 = l_Lean_Parser_mergeOrElseErrors(x_104, x_89, x_84);
lean_dec(x_84);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_99);
lean_dec(x_1);
x_106 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_107 = l_Lean_Parser_ParserState_mkNode(x_98, x_106, x_94);
x_108 = l_Lean_Parser_mergeOrElseErrors(x_107, x_89, x_84);
lean_dec(x_84);
return x_108;
}
}
else
{
lean_object* x_109; uint8_t x_110; 
lean_dec(x_96);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
x_110 = lean_nat_dec_eq(x_109, x_84);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = l_Lean_nullKind;
lean_inc(x_94);
x_112 = l_Lean_Parser_ParserState_mkNode(x_95, x_111, x_94);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = l_Lean_Parser_termParser___closed__2;
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lean_Parser_categoryParser___elambda__1(x_114, x_115, x_1, x_112);
x_117 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_118 = l_Lean_Parser_ParserState_mkNode(x_116, x_117, x_94);
x_119 = l_Lean_Parser_mergeOrElseErrors(x_118, x_89, x_84);
lean_dec(x_84);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
lean_dec(x_1);
x_120 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_121 = l_Lean_Parser_ParserState_mkNode(x_112, x_120, x_94);
x_122 = l_Lean_Parser_mergeOrElseErrors(x_121, x_89, x_84);
lean_dec(x_84);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_84);
x_123 = l_Lean_Parser_ParserState_restore(x_95, x_94, x_84);
x_124 = l_Lean_nullKind;
lean_inc(x_94);
x_125 = l_Lean_Parser_ParserState_mkNode(x_123, x_124, x_94);
x_126 = lean_ctor_get(x_125, 3);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = l_Lean_Parser_termParser___closed__2;
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_Parser_categoryParser___elambda__1(x_127, x_128, x_1, x_125);
x_130 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_131 = l_Lean_Parser_ParserState_mkNode(x_129, x_130, x_94);
x_132 = l_Lean_Parser_mergeOrElseErrors(x_131, x_89, x_84);
lean_dec(x_84);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_126);
lean_dec(x_1);
x_133 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_125, x_133, x_94);
x_135 = l_Lean_Parser_mergeOrElseErrors(x_134, x_89, x_84);
lean_dec(x_84);
return x_135;
}
}
}
}
block_143:
{
if (lean_obj_tag(x_140) == 0)
{
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_87);
x_95 = x_137;
goto block_136;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_137);
x_141 = l_Array_shrink___main___rarg(x_138, x_94);
lean_inc(x_84);
if (lean_is_scalar(x_87)) {
 x_142 = lean_alloc_ctor(0, 4, 0);
} else {
 x_142 = x_87;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_84);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_140);
x_95 = x_142;
goto block_136;
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_optIdent___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_majorPremise___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_majorPremise___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_majorPremise___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_majorPremise___closed__3;
x_2 = l_Lean_Parser_Tactic_majorPremise___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_majorPremise() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_majorPremise___closed__5;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductionAlt");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_inductionAlt___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_inductionAlt___closed__3;
x_2 = l_Lean_Parser_Term_fun___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_inductionAlt___closed__4;
x_2 = l_Lean_Parser_Term_matchAlt___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_Tactic_inductionAlt___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_inductionAlt___closed__7;
x_2 = l_Lean_Parser_Tactic_inductionAlt___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_inductionAlt___closed__1;
x_2 = l_Lean_Parser_Tactic_inductionAlt___closed__2;
x_3 = l_Lean_Parser_Tactic_inductionAlt___closed__9;
x_4 = l_Lean_Parser_nodeWithAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_inductionAlt___closed__10;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 2);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_FileMap_toPosition(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_inductionAlt;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_apply_2(x_15, x_7, x_8);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_55 = lean_ctor_get(x_7, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_FileMap_toPosition(x_56, x_23);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_nat_dec_le(x_13, x_58);
lean_dec(x_58);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__6;
x_61 = l_Lean_Parser_ParserState_mkError(x_19, x_60);
x_38 = x_61;
goto block_54;
}
else
{
x_38 = x_19;
goto block_54;
}
block_37:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
{
uint8_t _tmp_5 = x_3;
lean_object* _tmp_7 = x_24;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_sub(x_29, x_4);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_27, x_33, x_4);
return x_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_4);
return x_36;
}
else
{
lean_dec(x_4);
return x_27;
}
}
}
}
block_54:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_inc(x_7);
x_41 = l_Lean_Parser_tokenFn(x_7, x_38);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 2)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_48, x_40);
x_24 = x_49;
goto block_37;
}
else
{
lean_dec(x_40);
x_24 = x_41;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_50 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_50, x_40);
x_24 = x_51;
goto block_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_41, x_52, x_40);
x_24 = x_53;
goto block_37;
}
}
else
{
lean_dec(x_39);
x_24 = x_38;
goto block_37;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_62);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean_dec(x_17);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_nat_sub(x_68, x_4);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_66, x_72, x_4);
return x_73;
}
else
{
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_66, x_74, x_4);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = l_Lean_Parser_ParserState_popSyntax(x_66);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__11(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12(x_1, x_2, x_3, x_8, x_4, x_9, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Parser_Tactic_inductionAlts___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__2;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_12 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_11, x_3);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7(x_1, x_2, x_13, x_13, x_1, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_16 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_15, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__5;
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_17, x_3);
return x_18;
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_matchAlts___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_inductionAlt;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_inductionAlts___closed__1;
x_4 = l_Lean_Parser_sepBy1Info(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_matchAlts___closed__1;
x_2 = l_Lean_Parser_Tactic_inductionAlts___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_inductionAlts___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_inductionAlts___closed__3;
x_2 = l_Lean_Parser_Tactic_inductionAlts___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_inductionAlts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_inductionAlts___closed__5;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__2(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__4(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__3(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__6(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__8(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__10(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__9(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__12(x_1, x_2, x_9, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Tactic_inductionAlts___elambda__1___spec__11(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Parser_Tactic_withAlts___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_27; lean_object* x_28; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_27 = l_Lean_Parser_tokenFn(x_1, x_2);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 2)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Parser_Term_match___elambda__1___closed__8;
x_33 = lean_string_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Parser_Term_match___elambda__1___closed__12;
lean_inc(x_5);
x_35 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_34, x_5);
x_6 = x_35;
goto block_26;
}
else
{
x_6 = x_27;
goto block_26;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
x_36 = l_Lean_Parser_Term_match___elambda__1___closed__12;
lean_inc(x_5);
x_37 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_36, x_5);
x_6 = x_37;
goto block_26;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_38 = l_Lean_Parser_Term_match___elambda__1___closed__12;
lean_inc(x_5);
x_39 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_38, x_5);
x_6 = x_39;
goto block_26;
}
block_26:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_Tactic_inductionAlts___elambda__1(x_1, x_6);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_8, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_5);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = l_Lean_nullKind;
x_15 = l_Lean_Parser_ParserState_mkNode(x_8, x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Parser_ParserState_restore(x_8, x_4, x_5);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_4);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_19, x_5);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_6, x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_4);
return x_25;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_withAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_inductionAlts;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_match___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_withAlts___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_withAlts___closed__1;
x_2 = l_Lean_Parser_optionaInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_withAlts___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_withAlts___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_withAlts___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_withAlts___closed__2;
x_2 = l_Lean_Parser_Tactic_withAlts___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_withAlts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_withAlts___closed__4;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" using ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_usingRec___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_27; lean_object* x_28; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_27 = l_Lean_Parser_tokenFn(x_1, x_2);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 2)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2;
x_33 = lean_string_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5;
lean_inc(x_5);
x_35 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_34, x_5);
x_6 = x_35;
goto block_26;
}
else
{
x_6 = x_27;
goto block_26;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
x_36 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5;
lean_inc(x_5);
x_37 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_36, x_5);
x_6 = x_37;
goto block_26;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_38 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5;
lean_inc(x_5);
x_39 = l_Lean_Parser_ParserState_mkErrorsAt(x_27, x_38, x_5);
x_6 = x_39;
goto block_26;
}
block_26:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_ident___elambda__1(x_1, x_6);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_8, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_5);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = l_Lean_nullKind;
x_15 = l_Lean_Parser_ParserState_mkNode(x_8, x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Parser_ParserState_restore(x_8, x_4, x_5);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_4);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_19, x_5);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_6, x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_4);
return x_25;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_usingRec___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_usingRec___closed__2;
x_2 = l_Lean_Parser_optionaInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_usingRec___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_usingRec___closed__3;
x_2 = l_Lean_Parser_Tactic_usingRec___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_usingRec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_usingRec___closed__5;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" generalizing ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_generalizingVars___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_39; lean_object* x_40; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_39 = l_Lean_Parser_tokenFn(x_1, x_2);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 2)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2;
x_45 = lean_string_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5;
lean_inc(x_5);
x_47 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_46, x_5);
x_6 = x_47;
goto block_38;
}
else
{
x_6 = x_39;
goto block_38;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_48 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5;
lean_inc(x_5);
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_48, x_5);
x_6 = x_49;
goto block_38;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_50 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5;
lean_inc(x_5);
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_50, x_5);
x_6 = x_51;
goto block_38;
}
block_38:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_Parser_ident___elambda__1(x_1, x_6);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_revert___elambda__1___spec__1(x_1, x_10);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_9);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_13, x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_17, x_5);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = l_Lean_Parser_ParserState_mkNode(x_14, x_13, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Parser_ParserState_restore(x_14, x_4, x_5);
x_21 = l_Lean_Parser_ParserState_mkNode(x_20, x_13, x_4);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_1);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_10, x_22, x_9);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_22, x_4);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_nat_dec_eq(x_26, x_5);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = l_Lean_Parser_ParserState_mkNode(x_23, x_22, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_ParserState_restore(x_23, x_4, x_5);
x_30 = l_Lean_Parser_ParserState_mkNode(x_29, x_22, x_4);
return x_30;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_1);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
x_32 = lean_nat_dec_eq(x_31, x_5);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_6, x_33, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
x_36 = l_Lean_nullKind;
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_4);
return x_37;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_generalizingVars___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_generalizingVars___closed__2;
x_2 = l_Lean_Parser_optionaInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_generalizingVars___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_generalizingVars___closed__3;
x_2 = l_Lean_Parser_Tactic_generalizingVars___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_generalizingVars() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_generalizingVars___closed__5;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_induction___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_Tactic_induction___elambda__1___closed__4;
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
x_8 = l_Lean_Parser_Tactic_induction___elambda__1___closed__6;
x_9 = l_Lean_Parser_Tactic_induction___elambda__1___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Parser_nonReservedSymbolFnAux(x_8, x_9, x_1, x_2);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_majorPremise___elambda__1(x_1, x_10);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = l_Lean_Parser_Tactic_usingRec___elambda__1(x_1, x_12);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_16 = l_Lean_Parser_Tactic_generalizingVars___elambda__1(x_1, x_14);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Parser_Tactic_withAlts___elambda__1(x_1, x_16);
x_19 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_1);
x_21 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_16, x_21, x_7);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_1);
x_23 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_14, x_23, x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_1);
x_25 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_12, x_25, x_7);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_1);
x_27 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_10, x_27, x_7);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_1);
x_32 = lean_apply_2(x_4, x_1, x_2);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_nat_dec_eq(x_35, x_31);
lean_dec(x_35);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_31);
x_37 = l_Lean_Parser_ParserState_restore(x_32, x_30, x_31);
lean_dec(x_30);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
x_40 = l_Lean_Parser_Tactic_induction___elambda__1___closed__6;
x_41 = l_Lean_Parser_Tactic_induction___elambda__1___closed__8;
lean_inc(x_1);
x_42 = l_Lean_Parser_nonReservedSymbolFnAux(x_40, x_41, x_1, x_37);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_44 = l_Lean_Parser_Tactic_majorPremise___elambda__1(x_1, x_42);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_1);
x_46 = l_Lean_Parser_Tactic_usingRec___elambda__1(x_1, x_44);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_inc(x_1);
x_48 = l_Lean_Parser_Tactic_generalizingVars___elambda__1(x_1, x_46);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_Parser_Tactic_withAlts___elambda__1(x_1, x_48);
x_51 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_52 = l_Lean_Parser_ParserState_mkNode(x_50, x_51, x_39);
x_53 = l_Lean_Parser_mergeOrElseErrors(x_52, x_34, x_31);
lean_dec(x_31);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
lean_dec(x_1);
x_54 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_55 = l_Lean_Parser_ParserState_mkNode(x_48, x_54, x_39);
x_56 = l_Lean_Parser_mergeOrElseErrors(x_55, x_34, x_31);
lean_dec(x_31);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_47);
lean_dec(x_1);
x_57 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_58 = l_Lean_Parser_ParserState_mkNode(x_46, x_57, x_39);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_34, x_31);
lean_dec(x_31);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_45);
lean_dec(x_1);
x_60 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_44, x_60, x_39);
x_62 = l_Lean_Parser_mergeOrElseErrors(x_61, x_34, x_31);
lean_dec(x_31);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_43);
lean_dec(x_1);
x_63 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_64 = l_Lean_Parser_ParserState_mkNode(x_42, x_63, x_39);
x_65 = l_Lean_Parser_mergeOrElseErrors(x_64, x_34, x_31);
lean_dec(x_31);
return x_65;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_generalizingVars;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_withAlts;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_usingRec;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_induction___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_majorPremise;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_induction___closed__3;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_induction___closed__1;
x_2 = l_Lean_Parser_Tactic_induction___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_induction___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_induction___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_induction___closed__6;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_induction___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_induction___closed__7;
x_2 = l_Lean_Parser_Tactic_induction___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_induction() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_induction___closed__9;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_induction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_Tactic_induction;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
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
x_1 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
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
x_45 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__3;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
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
x_49 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
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
x_18 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__4;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_26 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_30 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_106 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__3;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
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
x_110 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
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
x_112 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__10;
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
x_74 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__4;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_84 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_89 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___elambda__1___closed__7;
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
x_3 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__3;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Parser_Parser_11__antiquotNestedExpr___closed__1;
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
x_45 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
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
x_49 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
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
x_18 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_26 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_30 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_106 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
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
x_110 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
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
x_112 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
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
x_74 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
x_75 = lean_string_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_84 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_89 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
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
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_nestedTacticBlock___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__4;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__5;
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
x_1 = l_Lean_Parser_Tactic_nestedTacticBlock___closed__6;
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
x_47 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
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
x_49 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
x_50 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_49, x_39);
x_8 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
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
x_108 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
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
x_110 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
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
x_112 = l_Lean_Parser_Term_structInst___elambda__1___closed__14;
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
lean_object* initialize_Init_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Tactic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Term(lean_io_mk_world());
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
l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__1);
l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__2);
l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__3);
l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___elambda__1___closed__4);
l_Lean_Parser_Tactic_majorPremise___closed__1 = _init_l_Lean_Parser_Tactic_majorPremise___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___closed__1);
l_Lean_Parser_Tactic_majorPremise___closed__2 = _init_l_Lean_Parser_Tactic_majorPremise___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___closed__2);
l_Lean_Parser_Tactic_majorPremise___closed__3 = _init_l_Lean_Parser_Tactic_majorPremise___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___closed__3);
l_Lean_Parser_Tactic_majorPremise___closed__4 = _init_l_Lean_Parser_Tactic_majorPremise___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___closed__4);
l_Lean_Parser_Tactic_majorPremise___closed__5 = _init_l_Lean_Parser_Tactic_majorPremise___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise___closed__5);
l_Lean_Parser_Tactic_majorPremise = _init_l_Lean_Parser_Tactic_majorPremise();
lean_mark_persistent(l_Lean_Parser_Tactic_majorPremise);
l_Lean_Parser_Tactic_inductionAlt___closed__1 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__1);
l_Lean_Parser_Tactic_inductionAlt___closed__2 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__2);
l_Lean_Parser_Tactic_inductionAlt___closed__3 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__3);
l_Lean_Parser_Tactic_inductionAlt___closed__4 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__4);
l_Lean_Parser_Tactic_inductionAlt___closed__5 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__5);
l_Lean_Parser_Tactic_inductionAlt___closed__6 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__6);
l_Lean_Parser_Tactic_inductionAlt___closed__7 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__7);
l_Lean_Parser_Tactic_inductionAlt___closed__8 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__8);
l_Lean_Parser_Tactic_inductionAlt___closed__9 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__9);
l_Lean_Parser_Tactic_inductionAlt___closed__10 = _init_l_Lean_Parser_Tactic_inductionAlt___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt___closed__10);
l_Lean_Parser_Tactic_inductionAlt = _init_l_Lean_Parser_Tactic_inductionAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlt);
l_Lean_Parser_Tactic_inductionAlts___closed__1 = _init_l_Lean_Parser_Tactic_inductionAlts___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts___closed__1);
l_Lean_Parser_Tactic_inductionAlts___closed__2 = _init_l_Lean_Parser_Tactic_inductionAlts___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts___closed__2);
l_Lean_Parser_Tactic_inductionAlts___closed__3 = _init_l_Lean_Parser_Tactic_inductionAlts___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts___closed__3);
l_Lean_Parser_Tactic_inductionAlts___closed__4 = _init_l_Lean_Parser_Tactic_inductionAlts___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts___closed__4);
l_Lean_Parser_Tactic_inductionAlts___closed__5 = _init_l_Lean_Parser_Tactic_inductionAlts___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts___closed__5);
l_Lean_Parser_Tactic_inductionAlts = _init_l_Lean_Parser_Tactic_inductionAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_inductionAlts);
l_Lean_Parser_Tactic_withAlts___closed__1 = _init_l_Lean_Parser_Tactic_withAlts___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_withAlts___closed__1);
l_Lean_Parser_Tactic_withAlts___closed__2 = _init_l_Lean_Parser_Tactic_withAlts___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_withAlts___closed__2);
l_Lean_Parser_Tactic_withAlts___closed__3 = _init_l_Lean_Parser_Tactic_withAlts___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_withAlts___closed__3);
l_Lean_Parser_Tactic_withAlts___closed__4 = _init_l_Lean_Parser_Tactic_withAlts___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_withAlts___closed__4);
l_Lean_Parser_Tactic_withAlts = _init_l_Lean_Parser_Tactic_withAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_withAlts);
l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___elambda__1___closed__1);
l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___elambda__1___closed__2);
l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___elambda__1___closed__3);
l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___elambda__1___closed__4);
l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___elambda__1___closed__5);
l_Lean_Parser_Tactic_usingRec___closed__1 = _init_l_Lean_Parser_Tactic_usingRec___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___closed__1);
l_Lean_Parser_Tactic_usingRec___closed__2 = _init_l_Lean_Parser_Tactic_usingRec___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___closed__2);
l_Lean_Parser_Tactic_usingRec___closed__3 = _init_l_Lean_Parser_Tactic_usingRec___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___closed__3);
l_Lean_Parser_Tactic_usingRec___closed__4 = _init_l_Lean_Parser_Tactic_usingRec___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___closed__4);
l_Lean_Parser_Tactic_usingRec___closed__5 = _init_l_Lean_Parser_Tactic_usingRec___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec___closed__5);
l_Lean_Parser_Tactic_usingRec = _init_l_Lean_Parser_Tactic_usingRec();
lean_mark_persistent(l_Lean_Parser_Tactic_usingRec);
l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__1);
l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__2);
l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__3);
l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__4);
l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___elambda__1___closed__5);
l_Lean_Parser_Tactic_generalizingVars___closed__1 = _init_l_Lean_Parser_Tactic_generalizingVars___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___closed__1);
l_Lean_Parser_Tactic_generalizingVars___closed__2 = _init_l_Lean_Parser_Tactic_generalizingVars___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___closed__2);
l_Lean_Parser_Tactic_generalizingVars___closed__3 = _init_l_Lean_Parser_Tactic_generalizingVars___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___closed__3);
l_Lean_Parser_Tactic_generalizingVars___closed__4 = _init_l_Lean_Parser_Tactic_generalizingVars___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___closed__4);
l_Lean_Parser_Tactic_generalizingVars___closed__5 = _init_l_Lean_Parser_Tactic_generalizingVars___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars___closed__5);
l_Lean_Parser_Tactic_generalizingVars = _init_l_Lean_Parser_Tactic_generalizingVars();
lean_mark_persistent(l_Lean_Parser_Tactic_generalizingVars);
l_Lean_Parser_Tactic_induction___elambda__1___closed__1 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__1);
l_Lean_Parser_Tactic_induction___elambda__1___closed__2 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__2);
l_Lean_Parser_Tactic_induction___elambda__1___closed__3 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__3);
l_Lean_Parser_Tactic_induction___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__4);
l_Lean_Parser_Tactic_induction___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__5);
l_Lean_Parser_Tactic_induction___elambda__1___closed__6 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__6);
l_Lean_Parser_Tactic_induction___elambda__1___closed__7 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__7);
l_Lean_Parser_Tactic_induction___elambda__1___closed__8 = _init_l_Lean_Parser_Tactic_induction___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___elambda__1___closed__8);
l_Lean_Parser_Tactic_induction___closed__1 = _init_l_Lean_Parser_Tactic_induction___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__1);
l_Lean_Parser_Tactic_induction___closed__2 = _init_l_Lean_Parser_Tactic_induction___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__2);
l_Lean_Parser_Tactic_induction___closed__3 = _init_l_Lean_Parser_Tactic_induction___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__3);
l_Lean_Parser_Tactic_induction___closed__4 = _init_l_Lean_Parser_Tactic_induction___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__4);
l_Lean_Parser_Tactic_induction___closed__5 = _init_l_Lean_Parser_Tactic_induction___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__5);
l_Lean_Parser_Tactic_induction___closed__6 = _init_l_Lean_Parser_Tactic_induction___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__6);
l_Lean_Parser_Tactic_induction___closed__7 = _init_l_Lean_Parser_Tactic_induction___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__7);
l_Lean_Parser_Tactic_induction___closed__8 = _init_l_Lean_Parser_Tactic_induction___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__8);
l_Lean_Parser_Tactic_induction___closed__9 = _init_l_Lean_Parser_Tactic_induction___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_induction___closed__9);
l_Lean_Parser_Tactic_induction = _init_l_Lean_Parser_Tactic_induction();
lean_mark_persistent(l_Lean_Parser_Tactic_induction);
res = l___regBuiltinParser_Lean_Parser_Tactic_induction(lean_io_mk_world());
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
