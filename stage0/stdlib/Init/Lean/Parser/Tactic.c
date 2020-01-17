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
lean_object* l_Lean_Parser_Tactic_orelse___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___closed__7;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__4;
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__5;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__7;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7;
lean_object* l_Lean_Parser_Tactic_apply___closed__2;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__5;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_orelse___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_Tactic_seq;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__7;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlock(lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__6;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_have___closed__3;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly;
extern lean_object* l_Lean_Parser_Term_subtype___closed__1;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__3;
lean_object* l_Lean_Parser_Tactic_underscore___boxed(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__7;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___closed__7;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__1;
lean_object* l_Lean_Parser_Tactic_underscore(uint8_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__9;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_nestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_intros___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__6;
lean_object* l_Lean_Parser_Tactic_orelse___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__5;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___closed__5;
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__3;
lean_object* l_Lean_Parser_Tactic_apply___closed__5;
lean_object* l_Lean_Parser_Tactic_assumption___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__6;
lean_object* l_Lean_Parser_tacticParser(uint8_t, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__13;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__6;
lean_object* l_Lean_Parser_Tactic_assumption;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__1;
lean_object* l_Lean_Parser_Tactic_seq___closed__5;
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__2;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_seq___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__1;
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object*);
lean_object* l_Lean_Parser_Tactic_ident_x27___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__12;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_intros___closed__2;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___closed__2;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__13;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_apply(lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__10;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__6;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__7;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__11;
lean_object* l_Lean_Parser_Tactic_assumption___closed__2;
lean_object* l_Lean_Parser_Tactic_ident_x27;
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_intro___closed__7;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock;
extern lean_object* l_Lean_Parser_Term_explicitUniv___closed__4;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_ident___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_apply;
lean_object* l_Lean_Parser_Tactic_assumption___closed__5;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1;
extern lean_object* l_Lean_Parser_Term_seq___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__9;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_orelse;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
lean_object* l_Lean_Parser_Tactic_underscoreFn(uint8_t, lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__2;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__4;
lean_object* l_Lean_Parser_Tactic_assumption___closed__3;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__4;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__1;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__8;
lean_object* l_Lean_Parser_Term_tacticBlock;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___closed__6;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___closed__5;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1(lean_object*);
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6;
lean_object* l_String_trim(lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5;
lean_object* l_Lean_Parser_Tactic_apply___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_assumption(lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__2;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__1;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__2;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
lean_object* l_Lean_Parser_Tactic_underscoreFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__5;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___closed__3;
lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Parser_Tactic_intro___closed__3;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_orelse___closed__6;
lean_object* l_Lean_Parser_Tactic_intro___closed__5;
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__7;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__3;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object*);
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__5;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_intro;
lean_object* l_Lean_Parser_tacticParser___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Tactic_seq___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__3;
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_Tactic_seq___closed__4;
extern lean_object* l_Lean_Parser_Level_paren___closed__1;
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
lean_object* l_Lean_Parser_tacticParser(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_categoryParser(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_tacticParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_tacticParser(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_underscoreFn___rarg(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Name_appendIndexAfter___closed__1;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3;
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
x_21 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3;
x_22 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_21, x_3);
x_6 = x_22;
goto block_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_4, x_23, x_3);
x_6 = x_24;
goto block_13;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_7);
lean_dec(x_7);
x_9 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_10 = l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4;
x_11 = l_Lean_mkIdentFrom(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Parser_ParserState_pushSyntax(x_9, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Parser_Tactic_underscoreFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_underscoreFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_underscoreFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_Tactic_underscoreFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_Tactic_underscore(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_underscoreFn___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_identNoAntiquot___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_Tactic_underscore___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_Tactic_underscore(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Tactic_ident_x27___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = l_Lean_Parser_Tactic_underscoreFn___rarg(x_2, x_14);
x_16 = l_Lean_Parser_mergeOrElseErrors(x_15, x_11, x_8);
lean_dec(x_8);
return x_16;
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_ident_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_ident_x27___elambda__1), 3, 0);
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
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_13 = l_Lean_Parser_categoryParserFn(x_11, x_12, x_6, x_7);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_6);
x_25 = l_Lean_Parser_tokenFn(x_6, x_13);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 2)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Parser_Term_have___elambda__1___closed__7;
x_31 = lean_string_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_17);
x_33 = l_Lean_Parser_ParserState_mkErrorsAt(x_25, x_32, x_17);
x_18 = x_33;
goto block_24;
}
else
{
x_18 = x_25;
goto block_24;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_34 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_17);
x_35 = l_Lean_Parser_ParserState_mkErrorsAt(x_25, x_34, x_17);
x_18 = x_35;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_36 = l_Lean_Parser_Term_have___elambda__1___closed__10;
lean_inc(x_17);
x_37 = l_Lean_Parser_ParserState_mkErrorsAt(x_25, x_36, x_17);
x_18 = x_37;
goto block_24;
}
block_24:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
{
uint8_t _tmp_3 = x_2;
lean_object* _tmp_6 = x_18;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_6);
x_21 = l_Lean_Parser_ParserState_restore(x_18, x_16, x_17);
lean_dec(x_16);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_3);
return x_23;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_6);
if (x_4 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_38);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_3);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Parser_ParserState_restore(x_13, x_9, x_10);
lean_dec(x_9);
x_43 = l_Lean_nullKind;
x_44 = l_Lean_Parser_ParserState_mkNode(x_42, x_43, x_3);
return x_44;
}
}
}
}
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
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
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
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
lean_object* _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_seq___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Tactic_seq___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_seq___elambda__1___closed__5;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = 1;
x_19 = l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_17, x_18, x_1, x_2, x_14);
lean_dec(x_1);
x_20 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_16);
x_22 = l_Lean_Parser_mergeOrElseErrors(x_21, x_11, x_8);
lean_dec(x_8);
return x_22;
}
}
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Parser_categoryParser(x_1, x_2, x_3);
return x_4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq___elambda__1___closed__5;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Tactic_seq___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_seq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_seq___closed__4;
x_2 = l_Lean_Parser_Tactic_seq___closed__5;
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
x_1 = l_Lean_Parser_Tactic_seq___closed__6;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Tactic_seq___elambda__1___spec__2(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Parser_sepByFn___at_Lean_Parser_Tactic_seq___elambda__1___spec__1(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_intro___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Tactic_intro___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_intro___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Tactic_intro___elambda__1___closed__6;
x_18 = l_Lean_Parser_Tactic_intro___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_24 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_1, x_2, x_19);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_24, x_26, x_22);
x_28 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_16);
x_30 = l_Lean_Parser_mergeOrElseErrors(x_29, x_11, x_8);
lean_dec(x_8);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
x_32 = lean_nat_dec_eq(x_31, x_23);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_24, x_33, x_22);
x_35 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_16);
x_37 = l_Lean_Parser_mergeOrElseErrors(x_36, x_11, x_8);
lean_dec(x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = l_Lean_Parser_ParserState_restore(x_24, x_22, x_23);
x_39 = l_Lean_nullKind;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_22);
x_41 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_16);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_11, x_8);
lean_dec(x_8);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_44 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_19, x_44, x_16);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_11, x_8);
lean_dec(x_8);
return x_46;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_intro___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_5 = l_Lean_Parser_Tactic_intro;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Parser_Tactic_ident_x27___elambda__1(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
if (x_11 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Parser_manyAux___main___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_13);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_7, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_17;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_intros___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_intros___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Tactic_intros___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_intros___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Tactic_intros___elambda__1___closed__6;
x_18 = l_Lean_Parser_Tactic_intros___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_23, x_1, x_2, x_19);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_22);
x_27 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_16);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_11, x_8);
lean_dec(x_8);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_19, x_30, x_16);
x_32 = l_Lean_Parser_mergeOrElseErrors(x_31, x_11, x_8);
lean_dec(x_8);
return x_32;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_intros___elambda__1), 3, 0);
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
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Tactic_intros___elambda__1___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_intros(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Tactic_assumption___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__5;
x_18 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__7;
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_16);
x_22 = l_Lean_Parser_mergeOrElseErrors(x_21, x_11, x_8);
lean_dec(x_8);
return x_22;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_assumption___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_apply___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_apply___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Tactic_apply___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_apply___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Tactic_apply___elambda__1___closed__6;
x_18 = l_Lean_Parser_Tactic_apply___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_19);
x_24 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_16);
x_26 = l_Lean_Parser_mergeOrElseErrors(x_25, x_11, x_8);
lean_dec(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_2);
x_27 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_19, x_27, x_16);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_11, x_8);
lean_dec(x_8);
return x_29;
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
x_1 = l_Lean_Parser_Term_typeAscription___closed__2;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_apply___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_apply___elambda__1___closed__2;
x_5 = l_Lean_Parser_Tactic_apply;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_54; lean_object* x_55; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_54 = l_Lean_Parser_tokenFn(x_2, x_14);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 2)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_60 = lean_string_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_62 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_61, x_8);
x_17 = x_62;
goto block_53;
}
else
{
x_17 = x_54;
goto block_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_63 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_63, x_8);
x_17 = x_64;
goto block_53;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_65 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_65, x_8);
x_17 = x_66;
goto block_53;
}
block_53:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_19 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_2, x_17);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Parser_tokenFn(x_2, x_19);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_29, x_21);
x_31 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_16);
x_33 = l_Lean_Parser_mergeOrElseErrors(x_32, x_11, x_8);
lean_dec(x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_22, x_34, x_16);
x_36 = l_Lean_Parser_mergeOrElseErrors(x_35, x_11, x_8);
lean_dec(x_8);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_37 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_38 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_37, x_21);
x_39 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_16);
x_41 = l_Lean_Parser_mergeOrElseErrors(x_40, x_11, x_8);
lean_dec(x_8);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_23);
x_42 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_43 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_42, x_21);
x_44 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_16);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_11, x_8);
lean_dec(x_8);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_2);
x_47 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_19, x_47, x_16);
x_49 = l_Lean_Parser_mergeOrElseErrors(x_48, x_11, x_8);
lean_dec(x_8);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_17, x_50, x_16);
x_52 = l_Lean_Parser_mergeOrElseErrors(x_51, x_11, x_8);
lean_dec(x_8);
return x_52;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__1;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_54; lean_object* x_55; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_54 = l_Lean_Parser_tokenFn(x_2, x_14);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 2)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
x_60 = lean_string_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_8);
x_62 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_61, x_8);
x_17 = x_62;
goto block_53;
}
else
{
x_17 = x_54;
goto block_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_63 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_8);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_63, x_8);
x_17 = x_64;
goto block_53;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_65 = l_Lean_Parser_Term_structInst___elambda__1___closed__13;
lean_inc(x_8);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_65, x_8);
x_17 = x_66;
goto block_53;
}
block_53:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_19 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_2, x_17);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Parser_tokenFn(x_2, x_19);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__9;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__13;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_29, x_21);
x_31 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_16);
x_33 = l_Lean_Parser_mergeOrElseErrors(x_32, x_11, x_8);
lean_dec(x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_34 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_22, x_34, x_16);
x_36 = l_Lean_Parser_mergeOrElseErrors(x_35, x_11, x_8);
lean_dec(x_8);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_37 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__13;
x_38 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_37, x_21);
x_39 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_16);
x_41 = l_Lean_Parser_mergeOrElseErrors(x_40, x_11, x_8);
lean_dec(x_8);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_23);
x_42 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__13;
x_43 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_42, x_21);
x_44 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_16);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_11, x_8);
lean_dec(x_8);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_2);
x_47 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_19, x_47, x_16);
x_49 = l_Lean_Parser_mergeOrElseErrors(x_48, x_11, x_8);
lean_dec(x_8);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_17, x_50, x_16);
x_52 = l_Lean_Parser_mergeOrElseErrors(x_51, x_11, x_8);
lean_dec(x_8);
return x_52;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
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
lean_object* l_Lean_Parser_Tactic_orelse___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_3);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_2);
x_9 = l_Lean_Parser_tokenFn(x_2, x_6);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__2;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_16, x_8);
x_18 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_20 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Parser_categoryParserFn(x_20, x_21, x_2, x_9);
x_23 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_5);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_2);
x_25 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_26 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_25, x_8);
x_27 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_5);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_2);
x_29 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__5;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_29, x_8);
x_31 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_5);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_33 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_34 = l_Lean_Parser_ParserState_mkNode(x_6, x_33, x_5);
return x_34;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Parser_categoryParser(x_1, x_2, x_3);
return x_4;
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
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Tactic_orelse___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_2 = l_Lean_Parser_Tactic_orelse___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_orelse___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Tactic_orelse___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_orelse___closed__5;
x_2 = l_Lean_Parser_Tactic_orelse___closed__6;
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
x_1 = l_Lean_Parser_Tactic_orelse___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Tactic_orelse(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
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
x_1 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_54; lean_object* x_55; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_54 = l_Lean_Parser_tokenFn(x_2, x_14);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 2)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__6;
x_60 = lean_string_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_62 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_61, x_8);
x_17 = x_62;
goto block_53;
}
else
{
x_17 = x_54;
goto block_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_63 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_63, x_8);
x_17 = x_64;
goto block_53;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_65 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_54, x_65, x_8);
x_17 = x_66;
goto block_53;
}
block_53:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_19 = l_Lean_Parser_Tactic_seq___elambda__1(x_1, x_2, x_17);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Parser_tokenFn(x_2, x_19);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__8;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_29, x_21);
x_31 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_16);
x_33 = l_Lean_Parser_mergeOrElseErrors(x_32, x_11, x_8);
lean_dec(x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_34 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_35 = l_Lean_Parser_ParserState_mkNode(x_22, x_34, x_16);
x_36 = l_Lean_Parser_mergeOrElseErrors(x_35, x_11, x_8);
lean_dec(x_8);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_37 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_38 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_37, x_21);
x_39 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_16);
x_41 = l_Lean_Parser_mergeOrElseErrors(x_40, x_11, x_8);
lean_dec(x_8);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_23);
x_42 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__11;
x_43 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_42, x_21);
x_44 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_16);
x_46 = l_Lean_Parser_mergeOrElseErrors(x_45, x_11, x_8);
lean_dec(x_8);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_2);
x_47 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_19, x_47, x_16);
x_49 = l_Lean_Parser_mergeOrElseErrors(x_48, x_11, x_8);
lean_dec(x_8);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_51 = l_Lean_Parser_ParserState_mkNode(x_17, x_50, x_16);
x_52 = l_Lean_Parser_mergeOrElseErrors(x_51, x_11, x_8);
lean_dec(x_8);
return x_52;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticBlock___elambda__1), 3, 0);
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
x_4 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_5 = l_Lean_Parser_Term_tacticBlock;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stxQuot");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`(tactic|");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_inc(x_1);
x_39 = l_Lean_Parser_tokenFn(x_1, x_2);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 2)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4;
x_45 = lean_string_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7;
x_47 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_46, x_38);
x_5 = x_47;
goto block_37;
}
else
{
lean_dec(x_38);
x_5 = x_39;
goto block_37;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_48 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_48, x_38);
x_5 = x_49;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_50 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_50, x_38);
x_5 = x_51;
goto block_37;
}
block_37:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_9 = l_Lean_Parser_categoryParserFn(x_7, x_8, x_1, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_Lean_Parser_tokenFn(x_1, x_9);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Parser_Level_paren___elambda__1___closed__8;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_19, x_11);
x_21 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_23 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_12, x_23, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_25 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_26 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_25, x_11);
x_27 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_29 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_29, x_11);
x_31 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_4);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_1);
x_33 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_9, x_33, x_4);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_1);
x_35 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_5, x_35, x_4);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_seq___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Level_paren___closed__4;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
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
x_1 = l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Term_tacticStxQuot___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticStxQuot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticStxQuot___elambda__1___boxed), 1, 0);
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
lean_object* l_Lean_Parser_Term_tacticStxQuot___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Term_tacticStxQuot___elambda__1(x_1);
lean_dec(x_1);
return x_2;
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
x_1 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_2 = l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
x_4 = l___regBuiltinParser_Lean_Parser_Term_tacticStxQuot___closed__2;
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
l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1 = _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___rarg___closed__1);
l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2 = _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___rarg___closed__2);
l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3 = _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___rarg___closed__3);
l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4 = _init_l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_underscoreFn___rarg___closed__4);
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
l_Lean_Parser_Tactic_seq___elambda__1___closed__4 = _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___elambda__1___closed__4);
l_Lean_Parser_Tactic_seq___elambda__1___closed__5 = _init_l_Lean_Parser_Tactic_seq___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___elambda__1___closed__5);
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
l_Lean_Parser_Tactic_seq___closed__6 = _init_l_Lean_Parser_Tactic_seq___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_seq___closed__6);
l_Lean_Parser_Tactic_seq = _init_l_Lean_Parser_Tactic_seq();
lean_mark_persistent(l_Lean_Parser_Tactic_seq);
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
l_Lean_Parser_Tactic_orelse___closed__7 = _init_l_Lean_Parser_Tactic_orelse___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_orelse___closed__7);
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
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__4);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__5);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__6);
l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_tacticStxQuot___elambda__1___rarg___closed__7);
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
