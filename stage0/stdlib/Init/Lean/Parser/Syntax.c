// Lean compiler output
// Module: Init.Lean.Parser.Syntax
// Imports: Init.Lean.Parser.Command
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
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_many___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_str___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_Lean_Parser_Syntax_try___closed__5;
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7;
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_Syntax_many1;
lean_object* l_Lean_Parser_Syntax_many___elambda__1___closed__2;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_lookahead___closed__4;
lean_object* l_Lean_Parser_Syntax_num___closed__5;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_try___closed__3;
lean_object* l_Lean_Parser_Syntax_many1___elambda__1___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Syntax_paren___closed__6;
lean_object* l_Lean_Parser_Command_syntax___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__6;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2;
extern lean_object* l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
lean_object* l_Lean_Parser_Syntax_paren___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_paren___closed__4;
lean_object* l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_cat___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_cat(lean_object*);
lean_object* l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__3;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
lean_object* l_Lean_Parser_Syntax_many___closed__1;
lean_object* l_Lean_Parser_Syntax_many___closed__2;
lean_object* l_Lean_Parser_Syntax_many___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_many(lean_object*);
lean_object* l_Lean_Parser_Syntax_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_lookahead___closed__5;
lean_object* l_Lean_Parser_Syntax_str___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__5;
lean_object* l_Lean_Parser_Syntax_paren;
lean_object* l_Lean_Parser_Syntax_paren___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_try(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_str___closed__5;
extern lean_object* l_Lean_Parser_Level_num___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__6;
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_cat___closed__2;
lean_object* l_Lean_Parser_addBuiltinParser(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__4;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_paren___closed__3;
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__6;
extern lean_object* l_Lean_Parser_strLit___closed__1;
lean_object* l_Lean_Parser_Syntax_many1___closed__4;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__8;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__4;
lean_object* l_Lean_Parser_Syntax_str___closed__4;
lean_object* l_Lean_Parser_Command_syntax;
lean_object* l_Lean_Parser_Command_syntax___closed__5;
lean_object* l_Lean_Parser_Syntax_lookahead___closed__6;
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__6;
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6;
lean_object* l_Lean_Parser_Syntax_paren___closed__1;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_cat___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_orelse(lean_object*);
lean_object* l_Lean_Parser_syntaxParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_num;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8;
lean_object* l_Lean_Parser_Syntax_num___closed__3;
lean_object* l_Lean_Parser_Syntax_try___closed__4;
lean_object* l_Lean_Parser_regSyntaxParserAttribute___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regSyntaxParserAttribute___closed__1;
lean_object* l_Lean_Parser_Syntax_many1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_lookahead(lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many1___closed__2;
lean_object* l_Lean_Parser_Syntax_sepBy1;
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__7;
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__2;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__4;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Syntax_str___closed__2;
lean_object* l_Lean_Parser_Syntax_optional___closed__4;
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__7;
lean_object* l_Lean_Parser_Command_syntax___closed__3;
lean_object* l_Lean_Parser_Syntax_orelse___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__4;
lean_object* l_Lean_Parser_Syntax_try___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_paren___elambda__1___closed__1;
lean_object* l_Lean_Parser_Command_syntax___closed__7;
lean_object* l_Lean_Parser_Syntax_str___closed__1;
lean_object* l_Lean_Parser_Syntax_paren___closed__5;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_paren___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_num___closed__2;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_num___closed__1;
lean_object* l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_num___closed__4;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_cat;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__4;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_lookahead___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_str(lean_object*);
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__11;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_Term_explicitBinder___closed__1;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8;
lean_object* l_Lean_Parser_Syntax_cat___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_num___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__2;
extern lean_object* l_Lean_Parser_Level_ident___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__1;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many___closed__3;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__6;
lean_object* l_Lean_Parser_Syntax_atom___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_sepBy(lean_object*);
lean_object* l_Lean_Parser_Syntax_atom;
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8;
extern lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
extern lean_object* l_Lean_Parser_Level_paren___closed__4;
extern lean_object* l_Lean_Parser_mkAntiquot___closed__7;
lean_object* l_Lean_Parser_Command_syntax___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_paren(lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_str___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_cat___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_optional;
lean_object* l_Lean_Parser_Syntax_atom___closed__1;
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_sepBy1(lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_paren___closed__2;
lean_object* l_Lean_Parser_Syntax_many1___closed__5;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_num(lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_atom___elambda__1___closed__4;
lean_object* l_Lean_Parser_Command_syntax___closed__6;
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_optional___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__6;
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_cat___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__1;
lean_object* l_Lean_Parser_categoryParser(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many1___closed__3;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_optional___closed__5;
lean_object* l_Lean_Parser_Syntax_atom___elambda__1___closed__2;
lean_object* l_Lean_Parser_regSyntaxParserAttribute(lean_object*);
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
extern lean_object* l_Lean_Parser_Term_typeAscription___closed__1;
lean_object* l_Lean_Parser_Syntax_atom___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_str___elambda__1___closed__1;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__6;
lean_object* l_Lean_Parser_strLitFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy1___closed__5;
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7;
lean_object* l_Lean_Parser_Syntax_atom___elambda__1___closed__3;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_object*);
lean_object* l_Lean_Parser_Syntax_atom___elambda__1___closed__1;
lean_object* l_Lean_Parser_Syntax_orelse___closed__2;
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__3;
lean_object* l_String_trim(lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__8;
lean_object* l_Lean_Parser_Syntax_orelse___closed__1;
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__8;
lean_object* l_Lean_Parser_Syntax_paren___closed__7;
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_str;
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_many;
lean_object* l_Lean_Parser_Syntax_try___closed__1;
extern lean_object* l_Lean_Parser_mkAntiquot___closed__6;
lean_object* l_Lean_Parser_Syntax_lookahead___closed__1;
lean_object* l_Lean_Parser_Syntax_try;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__7;
lean_object* l_Lean_Parser_mkAntiquot(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Syntax_optional___elambda__1___closed__6;
lean_object* l_Lean_Parser_Syntax_try___closed__2;
lean_object* l_Lean_Parser_Syntax_cat___closed__3;
lean_object* l_Lean_Parser_Syntax_lookahead___closed__2;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_lookahead;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__14;
lean_object* l_Lean_Parser_Syntax_atom___closed__2;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__3;
lean_object* l_Lean_Parser_Syntax_sepBy___closed__7;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_many___closed__4;
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_try___closed__6;
lean_object* l_Lean_Parser_Command_syntax___closed__2;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_atom(lean_object*);
lean_object* l_Lean_Parser_Syntax_optional___closed__2;
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__5;
lean_object* l_Lean_Parser_Syntax_orelse___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__9;
lean_object* l_Lean_Parser_Syntax_optional___closed__1;
lean_object* l_Lean_Parser_Syntax_cat___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_optional(lean_object*);
lean_object* l_Lean_Parser_Syntax_many1___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_syntax___elambda__1___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Command_syntax(lean_object*);
lean_object* l_Lean_Parser_Syntax_atom___closed__3;
extern lean_object* l_Lean_Parser_Term_orelse___elambda__1___closed__1;
lean_object* l_Lean_Parser_Command_syntax___closed__8;
lean_object* l_Lean_Parser_Syntax_num___elambda__1___closed__3;
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_many1(lean_object*);
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__2;
lean_object* l_Lean_Parser_Syntax_many___elambda__1___closed__4;
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6;
lean_object* l_Lean_Parser_Syntax_cat___elambda__1___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Syntax_orelse;
lean_object* l_Lean_Parser_Syntax_try___elambda__1___closed__5;
lean_object* l_Lean_Parser_Command_syntax___closed__4;
lean_object* l_Lean_Parser_syntaxParser(uint8_t, lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinSyntaxParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = 1;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_regSyntaxParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regSyntaxParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regSyntaxParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regSyntaxParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regSyntaxParserAttribute___closed__2;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_syntaxParser(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_categoryParser(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_syntaxParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_syntaxParser(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_10 = l_Lean_Parser_categoryParserFn(x_8, x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_7, x_12);
lean_dec(x_12);
lean_dec(x_7);
if (x_13 == 0)
{
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_10, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_3);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_7, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_restore(x_10, x_6, x_7);
lean_dec(x_6);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Syntax_paren___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_3 = l_Lean_Parser_Syntax_paren___elambda__1___closed__4;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Syntax_paren___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_paren___elambda__1___closed__5;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_49; lean_object* x_67; lean_object* x_68; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_67 = l_Lean_Parser_tokenFn(x_2, x_14);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 2)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Parser_Level_paren___elambda__1___closed__7;
x_73 = lean_string_dec_eq(x_71, x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Parser_Level_paren___elambda__1___closed__14;
lean_inc(x_8);
x_75 = l_Lean_Parser_ParserState_mkErrorsAt(x_67, x_74, x_8);
x_49 = x_75;
goto block_66;
}
else
{
x_49 = x_67;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
x_76 = l_Lean_Parser_Level_paren___elambda__1___closed__14;
lean_inc(x_8);
x_77 = l_Lean_Parser_ParserState_mkErrorsAt(x_67, x_76, x_8);
x_49 = x_77;
goto block_66;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
x_78 = l_Lean_Parser_Level_paren___elambda__1___closed__14;
lean_inc(x_8);
x_79 = l_Lean_Parser_ParserState_mkErrorsAt(x_67, x_78, x_8);
x_49 = x_79;
goto block_66;
}
block_48:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_Parser_tokenFn(x_2, x_17);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_Level_paren___elambda__1___closed__8;
x_26 = lean_string_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_28 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_27, x_19);
x_29 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_16);
x_31 = l_Lean_Parser_mergeOrElseErrors(x_30, x_11, x_8);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_19);
x_32 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_33 = l_Lean_Parser_ParserState_mkNode(x_20, x_32, x_16);
x_34 = l_Lean_Parser_mergeOrElseErrors(x_33, x_11, x_8);
lean_dec(x_8);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
x_35 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_36 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_35, x_19);
x_37 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_16);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_11, x_8);
lean_dec(x_8);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_21);
x_40 = l_Lean_Parser_Level_paren___elambda__1___closed__11;
x_41 = l_Lean_Parser_ParserState_mkErrorsAt(x_20, x_40, x_19);
x_42 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_43 = l_Lean_Parser_ParserState_mkNode(x_41, x_42, x_16);
x_44 = l_Lean_Parser_mergeOrElseErrors(x_43, x_11, x_8);
lean_dec(x_8);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_18);
lean_dec(x_2);
x_45 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_46 = l_Lean_Parser_ParserState_mkNode(x_17, x_45, x_16);
x_47 = l_Lean_Parser_mergeOrElseErrors(x_46, x_11, x_8);
lean_dec(x_8);
return x_47;
}
}
block_66:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_array_get_size(x_51);
lean_dec(x_51);
x_53 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_54 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_55 = l_Lean_Parser_categoryParserFn(x_53, x_54, x_2, x_49);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
lean_inc(x_2);
x_58 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1(x_57, x_1, x_2, x_55);
lean_dec(x_1);
x_59 = l_Lean_nullKind;
x_60 = l_Lean_Parser_ParserState_mkNode(x_58, x_59, x_52);
x_17 = x_60;
goto block_48;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_1);
x_61 = l_Lean_nullKind;
x_62 = l_Lean_Parser_ParserState_mkNode(x_55, x_61, x_52);
x_17 = x_62;
goto block_48;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_50);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_64 = l_Lean_Parser_ParserState_mkNode(x_49, x_63, x_16);
x_65 = l_Lean_Parser_mergeOrElseErrors(x_64, x_11, x_8);
lean_dec(x_8);
return x_65;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Parser_categoryParser(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_paren___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Level_paren___closed__4;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_explicitBinder___closed__1;
x_2 = l_Lean_Parser_Syntax_paren___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_2 = l_Lean_Parser_Syntax_paren___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__5;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_paren___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_paren___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___closed__5;
x_2 = l_Lean_Parser_Syntax_paren___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_paren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_paren___closed__7;
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_paren(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_paren___elambda__1___closed__3;
x_5 = l_Lean_Parser_Syntax_paren;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cat");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_cat___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_cat___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_cat___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_cat___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Syntax_cat___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Syntax_cat___elambda__1___closed__4;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_apply_3(x_7, x_1, x_2, x_3);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_10);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_10);
x_16 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_apply_3(x_5, x_1, x_2, x_16);
x_20 = l_Lean_Parser_Syntax_cat___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_18);
x_22 = l_Lean_Parser_mergeOrElseErrors(x_21, x_13, x_10);
lean_dec(x_10);
return x_22;
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_cat___elambda__1___closed__2;
x_4 = l_Lean_Parser_nodeInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_cat___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_cat___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_cat___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_cat___closed__2;
x_2 = l_Lean_Parser_Syntax_cat___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_cat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_cat___closed__4;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_cat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_cat___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_cat;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("atom");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_atom___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_atom___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_atom___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_atom___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Syntax_atom___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_atom___elambda__1___closed__4;
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
x_17 = l_Lean_Parser_strLitFn___rarg(x_2, x_14);
x_18 = l_Lean_Parser_Syntax_atom___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_16);
x_20 = l_Lean_Parser_mergeOrElseErrors(x_19, x_11, x_8);
lean_dec(x_8);
return x_20;
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_atom___elambda__1___closed__2;
x_2 = l_Lean_Parser_strLit___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_atom___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_atom___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_atom___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_atom___closed__2;
x_2 = l_Lean_Parser_Syntax_atom___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_atom() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_atom___closed__4;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_atom(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_atom___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_atom;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Level_num___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_num___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Level_num___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_num___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Level_num___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_num___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_num___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_num___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_num___elambda__1___closed__3;
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
x_17 = l_Lean_Parser_Syntax_num___elambda__1___closed__4;
x_18 = l_Lean_Parser_Syntax_num___elambda__1___closed__6;
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = l_Lean_Parser_Syntax_num___elambda__1___closed__1;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_16);
x_22 = l_Lean_Parser_mergeOrElseErrors(x_21, x_11, x_8);
lean_dec(x_8);
return x_22;
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_num___elambda__1___closed__4;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_num___elambda__1___closed__1;
x_2 = l_Lean_Parser_Syntax_num___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_num___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_num___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_num___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_num___closed__3;
x_2 = l_Lean_Parser_Syntax_num___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_num() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_num___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_num(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_num___elambda__1___closed__1;
x_5 = l_Lean_Parser_Syntax_num;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_str___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_str___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_str___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_str___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_str___elambda__1___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_str___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_str___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_str___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_str___elambda__1___closed__3;
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
x_17 = l_Lean_Parser_Syntax_str___elambda__1___closed__4;
x_18 = l_Lean_Parser_Syntax_str___elambda__1___closed__6;
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = l_Lean_Parser_Syntax_str___elambda__1___closed__1;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_16);
x_22 = l_Lean_Parser_mergeOrElseErrors(x_21, x_11, x_8);
lean_dec(x_8);
return x_22;
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_str___elambda__1___closed__4;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_str___elambda__1___closed__1;
x_2 = l_Lean_Parser_Syntax_str___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_str___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_str___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_str___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_str___closed__3;
x_2 = l_Lean_Parser_Syntax_str___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_str() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_str___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_str(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_str___elambda__1___closed__1;
x_5 = l_Lean_Parser_Syntax_str;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("try");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_try___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_try___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_try___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("try ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_try___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_try___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_try___elambda__1___closed__4;
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
x_17 = l_Lean_Parser_Syntax_try___elambda__1___closed__6;
x_18 = l_Lean_Parser_Syntax_try___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_19);
x_24 = l_Lean_Parser_Syntax_try___elambda__1___closed__2;
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
x_27 = l_Lean_Parser_Syntax_try___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_19, x_27, x_16);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_11, x_8);
lean_dec(x_8);
return x_29;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_paren___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_try___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_try___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_try___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_try___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_try___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_try___closed__4;
x_2 = l_Lean_Parser_Syntax_try___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_try() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_try___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_try(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_try___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_try;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lookahead");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lookahead ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_lookahead___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4;
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
x_17 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6;
x_18 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_19);
x_24 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
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
x_27 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_19, x_27, x_16);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_11, x_8);
lean_dec(x_8);
return x_29;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_paren___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_lookahead___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_lookahead___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_lookahead___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_lookahead___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_lookahead___closed__4;
x_2 = l_Lean_Parser_Syntax_lookahead___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_lookahead() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_lookahead___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_lookahead(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_lookahead;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_sepBy___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4;
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
x_17 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6;
x_18 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_23 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_19);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_23);
x_26 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_16);
x_28 = l_Lean_Parser_mergeOrElseErrors(x_27, x_11, x_8);
lean_dec(x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_2);
x_29 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_30 = l_Lean_Parser_ParserState_mkNode(x_23, x_29, x_16);
x_31 = l_Lean_Parser_mergeOrElseErrors(x_30, x_11, x_8);
lean_dec(x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_2);
x_32 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_19, x_32, x_16);
x_34 = l_Lean_Parser_mergeOrElseErrors(x_33, x_11, x_8);
lean_dec(x_8);
return x_34;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_2);
x_3 = l_Lean_Parser_andthenInfo(x_2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy___closed__1;
x_2 = l_Lean_Parser_Syntax_sepBy___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_sepBy___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_sepBy___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_sepBy___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy___closed__5;
x_2 = l_Lean_Parser_Syntax_sepBy___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_sepBy___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_sepBy(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_sepBy;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy1");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1;
x_3 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sepBy1 ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_sepBy1___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4;
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
x_17 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6;
x_18 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8;
lean_inc(x_2);
x_19 = l_Lean_Parser_nonReservedSymbolFnAux(x_17, x_18, x_2, x_14);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_23 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_19);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Parser_categoryParserFn(x_21, x_22, x_2, x_23);
x_26 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_16);
x_28 = l_Lean_Parser_mergeOrElseErrors(x_27, x_11, x_8);
lean_dec(x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_2);
x_29 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_30 = l_Lean_Parser_ParserState_mkNode(x_23, x_29, x_16);
x_31 = l_Lean_Parser_mergeOrElseErrors(x_30, x_11, x_8);
lean_dec(x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_2);
x_32 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_19, x_32, x_16);
x_34 = l_Lean_Parser_mergeOrElseErrors(x_33, x_11, x_8);
lean_dec(x_8);
return x_34;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6;
x_2 = 0;
x_3 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy1___closed__1;
x_2 = l_Lean_Parser_Syntax_sepBy___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_sepBy1___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_sepBy1___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_sepBy1___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_sepBy1___closed__4;
x_2 = l_Lean_Parser_Syntax_sepBy1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_sepBy1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_sepBy1___closed__6;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_sepBy1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_sepBy1;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("many");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_many___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_mkAntiquot___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_many___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Syntax_many___elambda__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_many___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_Parser_mkAntiquot___closed__6;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Parser_Syntax_many___elambda__1___closed__5;
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_16, x_8);
x_18 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_20 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_9, x_20, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_22 = l_Lean_Parser_Syntax_many___elambda__1___closed__5;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_22, x_8);
x_24 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_26 = l_Lean_Parser_Syntax_many___elambda__1___closed__5;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_26, x_8);
x_28 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_5);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_6, x_30, x_5);
return x_31;
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_mkAntiquot___closed__7;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_many___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_many___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_many___closed__2;
x_2 = l_Lean_Parser_Syntax_many___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_many___closed__4;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_many(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_many___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_many;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("many1");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_many1___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_many1___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_16, x_8);
x_18 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_20 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_9, x_20, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_22 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_22, x_8);
x_24 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_26 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_26, x_8);
x_28 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_5);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_6, x_30, x_5);
return x_31;
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Syntax_many1___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_many1___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_many1___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_many1___closed__3;
x_2 = l_Lean_Parser_Syntax_many1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_many1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_many1___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_many1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_many1___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_many1;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optional");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_optional___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Syntax_optional___elambda__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_optional___elambda__1___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Syntax_optional___elambda__1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_optional___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_Parser_Syntax_optional___elambda__1___closed__3;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Parser_Syntax_optional___elambda__1___closed__6;
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_16, x_8);
x_18 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_20 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_9, x_20, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_22 = l_Lean_Parser_Syntax_optional___elambda__1___closed__6;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_22, x_8);
x_24 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_26 = l_Lean_Parser_Syntax_optional___elambda__1___closed__6;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_26, x_8);
x_28 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_5);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_6, x_30, x_5);
return x_31;
}
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Syntax_optional___elambda__1___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Syntax_optional___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_2 = l_Lean_Parser_Syntax_optional___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_optional___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_optional___closed__3;
x_2 = l_Lean_Parser_Syntax_optional___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_optional() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_optional___closed__5;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_optional(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_optional___elambda__1___closed__2;
x_5 = l_Lean_Parser_Syntax_optional;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Syntax_orelse___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_paren___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_orelse___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Syntax_orelse___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Term_orelse___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_apply_3(x_5, x_1, x_2, x_3);
x_9 = l_Lean_Parser_Syntax_orelse___elambda__1___closed__1;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_7);
return x_10;
}
}
lean_object* _init_l_Lean_Parser_Syntax_orelse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_orelse___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Syntax_orelse___elambda__1___closed__1;
x_4 = l_Lean_Parser_nodeInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Syntax_orelse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Syntax_orelse___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Syntax_orelse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_orelse___closed__1;
x_2 = l_Lean_Parser_Syntax_orelse___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Syntax_orelse() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Syntax_orelse___closed__3;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Syntax_orelse(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_Syntax_orelse___elambda__1___closed__1;
x_5 = l_Lean_Parser_Syntax_orelse;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
x_3 = l_Lean_Parser_Command_syntax___elambda__1___closed__2;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_syntax___elambda__1___closed__4;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Command_syntax___elambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_syntax___elambda__1___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_syntax___elambda__1___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Command_syntax___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Command_syntax___elambda__1___closed__3;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_apply_3(x_7, x_1, x_2, x_3);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_10);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_52; lean_object* x_70; lean_object* x_71; 
lean_inc(x_10);
x_16 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_2);
x_70 = l_Lean_Parser_tokenFn(x_2, x_16);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 2)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Parser_Command_syntax___elambda__1___closed__5;
x_76 = lean_string_dec_eq(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Lean_Parser_Command_syntax___elambda__1___closed__8;
lean_inc(x_10);
x_78 = l_Lean_Parser_ParserState_mkErrorsAt(x_70, x_77, x_10);
x_52 = x_78;
goto block_69;
}
else
{
x_52 = x_70;
goto block_69;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_73);
x_79 = l_Lean_Parser_Command_syntax___elambda__1___closed__8;
lean_inc(x_10);
x_80 = l_Lean_Parser_ParserState_mkErrorsAt(x_70, x_79, x_10);
x_52 = x_80;
goto block_69;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
x_81 = l_Lean_Parser_Command_syntax___elambda__1___closed__8;
lean_inc(x_10);
x_82 = l_Lean_Parser_ParserState_mkErrorsAt(x_70, x_81, x_10);
x_52 = x_82;
goto block_69;
}
block_51:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_inc(x_2);
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
x_27 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__6;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_29, x_21);
x_31 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_18);
x_33 = l_Lean_Parser_mergeOrElseErrors(x_32, x_13, x_10);
lean_dec(x_10);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_21);
x_34 = lean_apply_3(x_5, x_1, x_2, x_22);
x_35 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_18);
x_37 = l_Lean_Parser_mergeOrElseErrors(x_36, x_13, x_10);
lean_dec(x_10);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__9;
x_39 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_38, x_21);
x_40 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_18);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_13, x_10);
lean_dec(x_10);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__9;
x_44 = l_Lean_Parser_ParserState_mkErrorsAt(x_22, x_43, x_21);
x_45 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_18);
x_47 = l_Lean_Parser_mergeOrElseErrors(x_46, x_13, x_10);
lean_dec(x_10);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_49 = l_Lean_Parser_ParserState_mkNode(x_19, x_48, x_18);
x_50 = l_Lean_Parser_mergeOrElseErrors(x_49, x_13, x_10);
lean_dec(x_10);
return x_50;
}
}
block_69:
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_57 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_58 = l_Lean_Parser_categoryParserFn(x_56, x_57, x_2, x_52);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = 0;
lean_inc(x_2);
x_61 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Syntax_paren___elambda__1___spec__1(x_60, x_1, x_2, x_58);
x_62 = l_Lean_nullKind;
x_63 = l_Lean_Parser_ParserState_mkNode(x_61, x_62, x_55);
x_19 = x_63;
goto block_51;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_58, x_64, x_55);
x_19 = x_65;
goto block_51;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_66 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_67 = l_Lean_Parser_ParserState_mkNode(x_52, x_66, x_18);
x_68 = l_Lean_Parser_mergeOrElseErrors(x_67, x_13, x_10);
lean_dec(x_10);
return x_68;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_syntax___elambda__1___closed__5;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_typeAscription___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_paren___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Command_syntax___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_syntax___closed__1;
x_2 = l_Lean_Parser_Command_syntax___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_2 = l_Lean_Parser_Command_syntax___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Command_syntax___elambda__1___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Command_syntax___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Command_syntax___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_syntax___closed__6;
x_2 = l_Lean_Parser_Command_syntax___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Command_syntax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_syntax___closed__8;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Command_syntax(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_4 = l_Lean_Parser_Command_syntax___elambda__1___closed__1;
x_5 = l_Lean_Parser_Command_syntax;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Lean_Parser_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regSyntaxParserAttribute___closed__1 = _init_l_Lean_Parser_regSyntaxParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regSyntaxParserAttribute___closed__1);
l_Lean_Parser_regSyntaxParserAttribute___closed__2 = _init_l_Lean_Parser_regSyntaxParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regSyntaxParserAttribute___closed__2);
res = l_Lean_Parser_regSyntaxParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_paren___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___elambda__1___closed__1);
l_Lean_Parser_Syntax_paren___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___elambda__1___closed__2);
l_Lean_Parser_Syntax_paren___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___elambda__1___closed__3);
l_Lean_Parser_Syntax_paren___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___elambda__1___closed__4);
l_Lean_Parser_Syntax_paren___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_paren___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___elambda__1___closed__5);
l_Lean_Parser_Syntax_paren___closed__1 = _init_l_Lean_Parser_Syntax_paren___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__1);
l_Lean_Parser_Syntax_paren___closed__2 = _init_l_Lean_Parser_Syntax_paren___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__2);
l_Lean_Parser_Syntax_paren___closed__3 = _init_l_Lean_Parser_Syntax_paren___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__3);
l_Lean_Parser_Syntax_paren___closed__4 = _init_l_Lean_Parser_Syntax_paren___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__4);
l_Lean_Parser_Syntax_paren___closed__5 = _init_l_Lean_Parser_Syntax_paren___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__5);
l_Lean_Parser_Syntax_paren___closed__6 = _init_l_Lean_Parser_Syntax_paren___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__6);
l_Lean_Parser_Syntax_paren___closed__7 = _init_l_Lean_Parser_Syntax_paren___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_paren___closed__7);
l_Lean_Parser_Syntax_paren = _init_l_Lean_Parser_Syntax_paren();
lean_mark_persistent(l_Lean_Parser_Syntax_paren);
res = l___regBuiltinParser_Lean_Parser_Syntax_paren(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_cat___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___elambda__1___closed__1);
l_Lean_Parser_Syntax_cat___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___elambda__1___closed__2);
l_Lean_Parser_Syntax_cat___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___elambda__1___closed__3);
l_Lean_Parser_Syntax_cat___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_cat___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___elambda__1___closed__4);
l_Lean_Parser_Syntax_cat___closed__1 = _init_l_Lean_Parser_Syntax_cat___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___closed__1);
l_Lean_Parser_Syntax_cat___closed__2 = _init_l_Lean_Parser_Syntax_cat___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___closed__2);
l_Lean_Parser_Syntax_cat___closed__3 = _init_l_Lean_Parser_Syntax_cat___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___closed__3);
l_Lean_Parser_Syntax_cat___closed__4 = _init_l_Lean_Parser_Syntax_cat___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_cat___closed__4);
l_Lean_Parser_Syntax_cat = _init_l_Lean_Parser_Syntax_cat();
lean_mark_persistent(l_Lean_Parser_Syntax_cat);
res = l___regBuiltinParser_Lean_Parser_Syntax_cat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_atom___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___elambda__1___closed__1);
l_Lean_Parser_Syntax_atom___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___elambda__1___closed__2);
l_Lean_Parser_Syntax_atom___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___elambda__1___closed__3);
l_Lean_Parser_Syntax_atom___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_atom___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___elambda__1___closed__4);
l_Lean_Parser_Syntax_atom___closed__1 = _init_l_Lean_Parser_Syntax_atom___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___closed__1);
l_Lean_Parser_Syntax_atom___closed__2 = _init_l_Lean_Parser_Syntax_atom___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___closed__2);
l_Lean_Parser_Syntax_atom___closed__3 = _init_l_Lean_Parser_Syntax_atom___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___closed__3);
l_Lean_Parser_Syntax_atom___closed__4 = _init_l_Lean_Parser_Syntax_atom___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_atom___closed__4);
l_Lean_Parser_Syntax_atom = _init_l_Lean_Parser_Syntax_atom();
lean_mark_persistent(l_Lean_Parser_Syntax_atom);
res = l___regBuiltinParser_Lean_Parser_Syntax_atom(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_num___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__1);
l_Lean_Parser_Syntax_num___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__2);
l_Lean_Parser_Syntax_num___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__3);
l_Lean_Parser_Syntax_num___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__4);
l_Lean_Parser_Syntax_num___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__5);
l_Lean_Parser_Syntax_num___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_num___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_num___elambda__1___closed__6);
l_Lean_Parser_Syntax_num___closed__1 = _init_l_Lean_Parser_Syntax_num___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_num___closed__1);
l_Lean_Parser_Syntax_num___closed__2 = _init_l_Lean_Parser_Syntax_num___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_num___closed__2);
l_Lean_Parser_Syntax_num___closed__3 = _init_l_Lean_Parser_Syntax_num___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_num___closed__3);
l_Lean_Parser_Syntax_num___closed__4 = _init_l_Lean_Parser_Syntax_num___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_num___closed__4);
l_Lean_Parser_Syntax_num___closed__5 = _init_l_Lean_Parser_Syntax_num___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_num___closed__5);
l_Lean_Parser_Syntax_num = _init_l_Lean_Parser_Syntax_num();
lean_mark_persistent(l_Lean_Parser_Syntax_num);
res = l___regBuiltinParser_Lean_Parser_Syntax_num(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_str___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__1);
l_Lean_Parser_Syntax_str___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__2);
l_Lean_Parser_Syntax_str___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__3);
l_Lean_Parser_Syntax_str___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__4);
l_Lean_Parser_Syntax_str___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__5);
l_Lean_Parser_Syntax_str___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_str___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_str___elambda__1___closed__6);
l_Lean_Parser_Syntax_str___closed__1 = _init_l_Lean_Parser_Syntax_str___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_str___closed__1);
l_Lean_Parser_Syntax_str___closed__2 = _init_l_Lean_Parser_Syntax_str___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_str___closed__2);
l_Lean_Parser_Syntax_str___closed__3 = _init_l_Lean_Parser_Syntax_str___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_str___closed__3);
l_Lean_Parser_Syntax_str___closed__4 = _init_l_Lean_Parser_Syntax_str___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_str___closed__4);
l_Lean_Parser_Syntax_str___closed__5 = _init_l_Lean_Parser_Syntax_str___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_str___closed__5);
l_Lean_Parser_Syntax_str = _init_l_Lean_Parser_Syntax_str();
lean_mark_persistent(l_Lean_Parser_Syntax_str);
res = l___regBuiltinParser_Lean_Parser_Syntax_str(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_try___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__1);
l_Lean_Parser_Syntax_try___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__2);
l_Lean_Parser_Syntax_try___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__3);
l_Lean_Parser_Syntax_try___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__4);
l_Lean_Parser_Syntax_try___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__5);
l_Lean_Parser_Syntax_try___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__6);
l_Lean_Parser_Syntax_try___elambda__1___closed__7 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__7);
l_Lean_Parser_Syntax_try___elambda__1___closed__8 = _init_l_Lean_Parser_Syntax_try___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Syntax_try___elambda__1___closed__8);
l_Lean_Parser_Syntax_try___closed__1 = _init_l_Lean_Parser_Syntax_try___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__1);
l_Lean_Parser_Syntax_try___closed__2 = _init_l_Lean_Parser_Syntax_try___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__2);
l_Lean_Parser_Syntax_try___closed__3 = _init_l_Lean_Parser_Syntax_try___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__3);
l_Lean_Parser_Syntax_try___closed__4 = _init_l_Lean_Parser_Syntax_try___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__4);
l_Lean_Parser_Syntax_try___closed__5 = _init_l_Lean_Parser_Syntax_try___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__5);
l_Lean_Parser_Syntax_try___closed__6 = _init_l_Lean_Parser_Syntax_try___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_try___closed__6);
l_Lean_Parser_Syntax_try = _init_l_Lean_Parser_Syntax_try();
lean_mark_persistent(l_Lean_Parser_Syntax_try);
res = l___regBuiltinParser_Lean_Parser_Syntax_try(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__1);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__2);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__3);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__4);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__5);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__6);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__7);
l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8 = _init_l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___elambda__1___closed__8);
l_Lean_Parser_Syntax_lookahead___closed__1 = _init_l_Lean_Parser_Syntax_lookahead___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__1);
l_Lean_Parser_Syntax_lookahead___closed__2 = _init_l_Lean_Parser_Syntax_lookahead___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__2);
l_Lean_Parser_Syntax_lookahead___closed__3 = _init_l_Lean_Parser_Syntax_lookahead___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__3);
l_Lean_Parser_Syntax_lookahead___closed__4 = _init_l_Lean_Parser_Syntax_lookahead___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__4);
l_Lean_Parser_Syntax_lookahead___closed__5 = _init_l_Lean_Parser_Syntax_lookahead___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__5);
l_Lean_Parser_Syntax_lookahead___closed__6 = _init_l_Lean_Parser_Syntax_lookahead___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead___closed__6);
l_Lean_Parser_Syntax_lookahead = _init_l_Lean_Parser_Syntax_lookahead();
lean_mark_persistent(l_Lean_Parser_Syntax_lookahead);
res = l___regBuiltinParser_Lean_Parser_Syntax_lookahead(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__1);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__2);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__3);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__4);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__5);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__6);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__7);
l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8 = _init_l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___elambda__1___closed__8);
l_Lean_Parser_Syntax_sepBy___closed__1 = _init_l_Lean_Parser_Syntax_sepBy___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__1);
l_Lean_Parser_Syntax_sepBy___closed__2 = _init_l_Lean_Parser_Syntax_sepBy___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__2);
l_Lean_Parser_Syntax_sepBy___closed__3 = _init_l_Lean_Parser_Syntax_sepBy___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__3);
l_Lean_Parser_Syntax_sepBy___closed__4 = _init_l_Lean_Parser_Syntax_sepBy___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__4);
l_Lean_Parser_Syntax_sepBy___closed__5 = _init_l_Lean_Parser_Syntax_sepBy___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__5);
l_Lean_Parser_Syntax_sepBy___closed__6 = _init_l_Lean_Parser_Syntax_sepBy___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__6);
l_Lean_Parser_Syntax_sepBy___closed__7 = _init_l_Lean_Parser_Syntax_sepBy___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy___closed__7);
l_Lean_Parser_Syntax_sepBy = _init_l_Lean_Parser_Syntax_sepBy();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy);
res = l___regBuiltinParser_Lean_Parser_Syntax_sepBy(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__1);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__2);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__3);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__4);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__5);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__6);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__7);
l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8 = _init_l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___elambda__1___closed__8);
l_Lean_Parser_Syntax_sepBy1___closed__1 = _init_l_Lean_Parser_Syntax_sepBy1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__1);
l_Lean_Parser_Syntax_sepBy1___closed__2 = _init_l_Lean_Parser_Syntax_sepBy1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__2);
l_Lean_Parser_Syntax_sepBy1___closed__3 = _init_l_Lean_Parser_Syntax_sepBy1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__3);
l_Lean_Parser_Syntax_sepBy1___closed__4 = _init_l_Lean_Parser_Syntax_sepBy1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__4);
l_Lean_Parser_Syntax_sepBy1___closed__5 = _init_l_Lean_Parser_Syntax_sepBy1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__5);
l_Lean_Parser_Syntax_sepBy1___closed__6 = _init_l_Lean_Parser_Syntax_sepBy1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1___closed__6);
l_Lean_Parser_Syntax_sepBy1 = _init_l_Lean_Parser_Syntax_sepBy1();
lean_mark_persistent(l_Lean_Parser_Syntax_sepBy1);
res = l___regBuiltinParser_Lean_Parser_Syntax_sepBy1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_many___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_many___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_many___elambda__1___closed__1);
l_Lean_Parser_Syntax_many___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_many___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_many___elambda__1___closed__2);
l_Lean_Parser_Syntax_many___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_many___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_many___elambda__1___closed__3);
l_Lean_Parser_Syntax_many___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_many___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_many___elambda__1___closed__4);
l_Lean_Parser_Syntax_many___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_many___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_many___elambda__1___closed__5);
l_Lean_Parser_Syntax_many___closed__1 = _init_l_Lean_Parser_Syntax_many___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_many___closed__1);
l_Lean_Parser_Syntax_many___closed__2 = _init_l_Lean_Parser_Syntax_many___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_many___closed__2);
l_Lean_Parser_Syntax_many___closed__3 = _init_l_Lean_Parser_Syntax_many___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_many___closed__3);
l_Lean_Parser_Syntax_many___closed__4 = _init_l_Lean_Parser_Syntax_many___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_many___closed__4);
l_Lean_Parser_Syntax_many = _init_l_Lean_Parser_Syntax_many();
lean_mark_persistent(l_Lean_Parser_Syntax_many);
res = l___regBuiltinParser_Lean_Parser_Syntax_many(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_many1___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_many1___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___elambda__1___closed__1);
l_Lean_Parser_Syntax_many1___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_many1___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___elambda__1___closed__2);
l_Lean_Parser_Syntax_many1___closed__1 = _init_l_Lean_Parser_Syntax_many1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___closed__1);
l_Lean_Parser_Syntax_many1___closed__2 = _init_l_Lean_Parser_Syntax_many1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___closed__2);
l_Lean_Parser_Syntax_many1___closed__3 = _init_l_Lean_Parser_Syntax_many1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___closed__3);
l_Lean_Parser_Syntax_many1___closed__4 = _init_l_Lean_Parser_Syntax_many1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___closed__4);
l_Lean_Parser_Syntax_many1___closed__5 = _init_l_Lean_Parser_Syntax_many1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_many1___closed__5);
l_Lean_Parser_Syntax_many1 = _init_l_Lean_Parser_Syntax_many1();
lean_mark_persistent(l_Lean_Parser_Syntax_many1);
res = l___regBuiltinParser_Lean_Parser_Syntax_many1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_optional___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__1);
l_Lean_Parser_Syntax_optional___elambda__1___closed__2 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__2);
l_Lean_Parser_Syntax_optional___elambda__1___closed__3 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__3);
l_Lean_Parser_Syntax_optional___elambda__1___closed__4 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__4);
l_Lean_Parser_Syntax_optional___elambda__1___closed__5 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__5);
l_Lean_Parser_Syntax_optional___elambda__1___closed__6 = _init_l_Lean_Parser_Syntax_optional___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___elambda__1___closed__6);
l_Lean_Parser_Syntax_optional___closed__1 = _init_l_Lean_Parser_Syntax_optional___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___closed__1);
l_Lean_Parser_Syntax_optional___closed__2 = _init_l_Lean_Parser_Syntax_optional___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___closed__2);
l_Lean_Parser_Syntax_optional___closed__3 = _init_l_Lean_Parser_Syntax_optional___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___closed__3);
l_Lean_Parser_Syntax_optional___closed__4 = _init_l_Lean_Parser_Syntax_optional___closed__4();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___closed__4);
l_Lean_Parser_Syntax_optional___closed__5 = _init_l_Lean_Parser_Syntax_optional___closed__5();
lean_mark_persistent(l_Lean_Parser_Syntax_optional___closed__5);
l_Lean_Parser_Syntax_optional = _init_l_Lean_Parser_Syntax_optional();
lean_mark_persistent(l_Lean_Parser_Syntax_optional);
res = l___regBuiltinParser_Lean_Parser_Syntax_optional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Syntax_orelse___elambda__1___closed__1 = _init_l_Lean_Parser_Syntax_orelse___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_orelse___elambda__1___closed__1);
l_Lean_Parser_Syntax_orelse___closed__1 = _init_l_Lean_Parser_Syntax_orelse___closed__1();
lean_mark_persistent(l_Lean_Parser_Syntax_orelse___closed__1);
l_Lean_Parser_Syntax_orelse___closed__2 = _init_l_Lean_Parser_Syntax_orelse___closed__2();
lean_mark_persistent(l_Lean_Parser_Syntax_orelse___closed__2);
l_Lean_Parser_Syntax_orelse___closed__3 = _init_l_Lean_Parser_Syntax_orelse___closed__3();
lean_mark_persistent(l_Lean_Parser_Syntax_orelse___closed__3);
l_Lean_Parser_Syntax_orelse = _init_l_Lean_Parser_Syntax_orelse();
lean_mark_persistent(l_Lean_Parser_Syntax_orelse);
res = l___regBuiltinParser_Lean_Parser_Syntax_orelse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_syntax___elambda__1___closed__1 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__1);
l_Lean_Parser_Command_syntax___elambda__1___closed__2 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__2);
l_Lean_Parser_Command_syntax___elambda__1___closed__3 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__3);
l_Lean_Parser_Command_syntax___elambda__1___closed__4 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__4);
l_Lean_Parser_Command_syntax___elambda__1___closed__5 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__5);
l_Lean_Parser_Command_syntax___elambda__1___closed__6 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__6);
l_Lean_Parser_Command_syntax___elambda__1___closed__7 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__7);
l_Lean_Parser_Command_syntax___elambda__1___closed__8 = _init_l_Lean_Parser_Command_syntax___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Command_syntax___elambda__1___closed__8);
l_Lean_Parser_Command_syntax___closed__1 = _init_l_Lean_Parser_Command_syntax___closed__1();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__1);
l_Lean_Parser_Command_syntax___closed__2 = _init_l_Lean_Parser_Command_syntax___closed__2();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__2);
l_Lean_Parser_Command_syntax___closed__3 = _init_l_Lean_Parser_Command_syntax___closed__3();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__3);
l_Lean_Parser_Command_syntax___closed__4 = _init_l_Lean_Parser_Command_syntax___closed__4();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__4);
l_Lean_Parser_Command_syntax___closed__5 = _init_l_Lean_Parser_Command_syntax___closed__5();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__5);
l_Lean_Parser_Command_syntax___closed__6 = _init_l_Lean_Parser_Command_syntax___closed__6();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__6);
l_Lean_Parser_Command_syntax___closed__7 = _init_l_Lean_Parser_Command_syntax___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__7);
l_Lean_Parser_Command_syntax___closed__8 = _init_l_Lean_Parser_Command_syntax___closed__8();
lean_mark_persistent(l_Lean_Parser_Command_syntax___closed__8);
l_Lean_Parser_Command_syntax = _init_l_Lean_Parser_Command_syntax();
lean_mark_persistent(l_Lean_Parser_Command_syntax);
res = l___regBuiltinParser_Lean_Parser_Command_syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
