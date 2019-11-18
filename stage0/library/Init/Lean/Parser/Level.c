// Lean compiler output
// Module: Init.Lean.Parser.Level
// Imports: Init.Lean.Parser.Parser
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
lean_object* l_Lean_Parser_Level_max___closed__2;
lean_object* l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__5;
lean_object* l_Lean_Parser_mkLevelParserAttribute___closed__5;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_imax___closed__1;
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr___closed__3;
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkLevelParserAttribute(lean_object*);
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
lean_object* l_Lean_Parser_Level_paren;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
lean_object* l_Lean_Parser_Level_imax___closed__2;
lean_object* l_Lean_Parser_Level_hole___closed__4;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_max___elambda__1___closed__2;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_Level_max;
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_ident___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_max___elambda__1___closed__1;
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__1;
lean_object* l_Lean_Parser_Level_num___closed__3;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_builtinLevelParsingTable;
lean_object* l_Lean_Parser_mkLevelParserAttribute___closed__1;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_paren___closed__5;
lean_object* l_Lean_Parser_Level_addLit___closed__6;
lean_object* l_Lean_Parser_Level_hole___closed__2;
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
extern lean_object* l_Lean_Parser_appPrec;
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_addLit;
lean_object* l_Lean_Parser_Level_paren___closed__3;
lean_object* l_Lean_Parser_registerParserAttribute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_max___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__3;
lean_object* l_Lean_Parser_levelParser(uint8_t, lean_object*);
lean_object* l_Lean_Parser_Level_num;
lean_object* l_Lean_Parser_Level_paren___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Level_addLit(lean_object*);
lean_object* l_Lean_Parser_Level_max___elambda__1___closed__3;
lean_object* l_Lean_Parser_Level_paren___closed__1;
lean_object* l_Lean_Parser_Level_paren___closed__6;
lean_object* l_Lean_Parser_Level_num___elambda__1___boxed(lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Level_hole(lean_object*);
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__3;
lean_object* l_Lean_Parser_Level_num___closed__1;
lean_object* l_Lean_Parser_Level_paren___elambda__1(lean_object*);
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_max___closed__4;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_max___closed__1;
lean_object* l_Lean_Parser_Level_addLit___closed__5;
lean_object* l_Lean_Parser_Level_ident___closed__3;
lean_object* l_Lean_Parser_levelParser___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_levelParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
extern lean_object* l_Lean_Parser_Parser_inhabited___closed__1;
lean_object* l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
lean_object* l_Lean_Parser_levelParser___boxed(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__4;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_levelParserAttribute;
lean_object* l_Lean_Parser_mkLevelParserAttribute___closed__2;
lean_object* l_Lean_Parser_Level_paren___closed__7;
lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__2;
lean_object* l_Lean_Parser_Level_num___elambda__1(lean_object*);
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Level_imax(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_num___closed__2;
lean_object* l_Lean_Parser_Level_max___elambda__1___closed__4;
lean_object* l_Lean_Parser_Level_ident___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Parser_Level_ident___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
extern lean_object* l_Lean_Parser_ident___closed__1;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_Level_ident___elambda__1(lean_object*);
lean_object* l_Lean_Parser_Level_ident___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
lean_object* l_Lean_Parser_numLitFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_paren___closed__2;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7;
lean_object* l_Lean_Parser_Level_imax;
lean_object* l_Lean_Parser_Level_imax___closed__5;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__1;
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
extern lean_object* l_Lean_Parser_numLit___closed__1;
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr(lean_object*);
lean_object* l_Lean_Parser_Level_imax___closed__4;
lean_object* l_Lean_Parser_Level_hole___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_identFn___rarg(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Level_imax___closed__3;
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__4;
lean_object* l_Lean_Parser_Level_addLit___closed__1;
lean_object* l_Lean_Parser_Level_addLit___closed__7;
lean_object* l_Lean_Parser_Level_addLit___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_hole___closed__1;
lean_object* l_Lean_Parser_Level_hole___elambda__1(lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Level_max(lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo(lean_object*);
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_mkLevelParserAttribute___closed__3;
lean_object* l_Lean_Parser_Level_max___closed__5;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
lean_object* l_Lean_Parser_Level_num___elambda__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ParserAttribute_inhabited___closed__4;
lean_object* l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__1;
lean_object* l___regBuiltinParser_Lean_Parser_Level_num(lean_object*);
lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__1;
lean_object* l_Lean_Parser_Level_hole;
lean_object* l_Lean_Parser_Level_max___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Level_paren(lean_object*);
lean_object* l_Lean_Parser_Level_addLit___closed__3;
lean_object* l_Lean_Parser_Level_ident;
lean_object* l_Lean_Parser_Level_addLit___closed__2;
extern lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_Level_paren___closed__8;
lean_object* l_Lean_Parser_Level_imax___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Level_hole___closed__3;
lean_object* l_Lean_Parser_Level_imax___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkLevelParserAttribute___closed__4;
lean_object* l_Lean_Parser_Level_max___closed__3;
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5;
lean_object* l_Lean_Parser_Level_paren___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_Level_addLit___closed__4;
lean_object* l___regBuiltinParser_Lean_Parser_Level_ident(lean_object*);
lean_object* l_Lean_Parser_mkBuiltinParsingTablesRef(lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinLevelParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinLevelParsingTable");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinLevelParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_mkLevelParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("levelParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkLevelParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkLevelParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_mkLevelParserAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_builtinLevelParsingTable;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_mkLevelParserAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkLevelParserAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universe level parser");
return x_1;
}
}
lean_object* l_Lean_Parser_mkLevelParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_mkLevelParserAttribute___closed__2;
x_3 = l_Lean_Parser_mkLevelParserAttribute___closed__4;
x_4 = l_Lean_Parser_mkLevelParserAttribute___closed__5;
x_5 = l_Lean_Parser_mkLevelParserAttribute___closed__3;
x_6 = l_Lean_Parser_registerParserAttribute(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_levelParser___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_levelParserAttribute;
x_6 = l_Lean_Parser_ParserAttribute_runParser(x_5, x_1, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_levelParser(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_levelParser___lambda__1___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_levelParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_levelParser___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_levelParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_levelParser(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_44 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_45 = lean_string_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
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
x_48 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_48, x_38);
x_5 = x_49;
goto block_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_50 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
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
x_7 = l_Lean_Parser_levelParserAttribute;
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_9 = l_Lean_Parser_ParserAttribute_runParser(x_7, x_8, x_1, x_5);
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
x_17 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_19, x_11);
x_21 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_23 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_24 = l_Lean_Parser_ParserState_mkNode(x_12, x_23, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_25 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_26 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_25, x_11);
x_27 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_29 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_29, x_11);
x_31 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_4);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_1);
x_33 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_34 = l_Lean_Parser_ParserState_mkNode(x_9, x_33, x_4);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_1);
x_35 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_36 = l_Lean_Parser_ParserState_mkNode(x_5, x_35, x_4);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_Level_paren___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Level_paren___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___closed__2;
x_2 = l_Lean_Parser_Level_paren___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_2 = l_Lean_Parser_Level_paren___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_paren___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___closed__6;
x_2 = l_Lean_Parser_Level_paren___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_paren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_paren___closed__8;
return x_1;
}
}
lean_object* l_Lean_Parser_Level_paren___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Level_paren___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_4 = l_Lean_Parser_Level_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_Parser_levelParserAttribute;
x_9 = l_Lean_Parser_appPrec;
lean_inc(x_3);
x_10 = l_Lean_Parser_ParserAttribute_runParser(x_8, x_9, x_3, x_4);
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
lean_object* _init_l_Lean_Parser_Level_max___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_max___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_max___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_max___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_max___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__4;
lean_inc(x_2);
x_8 = l_Lean_Parser_symbolOrIdentFnAux(x_6, x_7, x_2, x_3);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = l_Lean_Parser_levelParserAttribute;
x_13 = l_Lean_Parser_appPrec;
lean_inc(x_2);
x_14 = l_Lean_Parser_ParserAttribute_runParser(x_12, x_13, x_2, x_8);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = 0;
x_17 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_16, x_1, x_2, x_14);
x_18 = l_Lean_nullKind;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_11);
x_20 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_2);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_11);
x_24 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_2);
x_26 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_8, x_26, x_5);
return x_27;
}
}
}
lean_object* _init_l_Lean_Parser_Level_max___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_max___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_max___closed__1;
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_max___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_2 = l_Lean_Parser_Level_max___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_max___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_max___elambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_max___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_max___closed__3;
x_2 = l_Lean_Parser_Level_max___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_max() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_max___closed__5;
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_Level_max___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Level_max___elambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_max(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_4 = l_Lean_Parser_Level_max;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_imax___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_7 = l_Lean_Parser_Level_imax___elambda__1___closed__4;
lean_inc(x_2);
x_8 = l_Lean_Parser_symbolOrIdentFnAux(x_6, x_7, x_2, x_3);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = l_Lean_Parser_levelParserAttribute;
x_13 = l_Lean_Parser_appPrec;
lean_inc(x_2);
x_14 = l_Lean_Parser_ParserAttribute_runParser(x_12, x_13, x_2, x_8);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = 0;
x_17 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_16, x_1, x_2, x_14);
x_18 = l_Lean_nullKind;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_11);
x_20 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_2);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_11);
x_24 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_2);
x_26 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_8, x_26, x_5);
return x_27;
}
}
}
lean_object* _init_l_Lean_Parser_Level_imax___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_imax___closed__1;
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_2 = l_Lean_Parser_Level_imax___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_imax___elambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_imax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_imax___closed__3;
x_2 = l_Lean_Parser_Level_imax___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_imax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_imax___closed__5;
return x_1;
}
}
lean_object* l_Lean_Parser_Level_imax___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Level_imax___elambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_imax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_4 = l_Lean_Parser_Level_imax;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_appendIndexAfter___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_12 = lean_string_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_13, x_5);
x_15 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_19 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_19, x_5);
x_21 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_23 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_23, x_5);
x_25 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
}
}
lean_object* l_Lean_Parser_Level_hole___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_hole___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_hole___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_hole___closed__2;
x_2 = l_Lean_Parser_Level_hole___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_hole() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_hole___closed__4;
return x_1;
}
}
lean_object* l_Lean_Parser_Level_hole___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Level_hole___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_hole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_4 = l_Lean_Parser_Level_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_num___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_numLitFn___rarg(x_1, x_2);
x_6 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_ParserState_mkNode(x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Parser_Level_num___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Level_num___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_num___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_numLit___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_num___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_num___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_num___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_num___closed__1;
x_2 = l_Lean_Parser_Level_num___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_num() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_num___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_Level_num___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Level_num___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_num(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_4 = l_Lean_Parser_Level_num;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_ident___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_6 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_7 = l_Lean_Parser_ParserState_mkNode(x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Parser_Level_ident___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Level_ident___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_ident___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_2 = l_Lean_Parser_ident___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_ident___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_ident___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_ident___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_ident___closed__1;
x_2 = l_Lean_Parser_Level_ident___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_ident() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_ident___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_Level_ident___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Level_ident___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_4 = l_Lean_Parser_Level_ident;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_LevelToFormat_Result_format___main___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Level_addLit___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_3);
x_14 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_2);
x_17 = l_Lean_Parser_tokenFn(x_2, x_14);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_23 = lean_string_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_24, x_16);
x_6 = x_25;
goto block_13;
}
else
{
lean_dec(x_16);
x_6 = x_17;
goto block_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_26 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_26, x_16);
x_6 = x_27;
goto block_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
x_28 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_28, x_16);
x_6 = x_29;
goto block_13;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_14, x_30, x_5);
return x_31;
}
block_13:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_numLitFn___rarg(x_2, x_6);
x_9 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_2);
x_11 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_6, x_11, x_5);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(65u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_2 = l_Lean_Parser_Level_addLit___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_addLit___closed__2;
x_2 = l_Lean_Parser_numLit___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Level_addLit___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_2 = l_Lean_Parser_Level_addLit___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Level_addLit___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_addLit___closed__5;
x_2 = l_Lean_Parser_Level_addLit___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Level_addLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Level_addLit___closed__7;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Level_addLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_4 = l_Lean_Parser_Level_addLit;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Parser_Parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Parser(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_mkBuiltinParsingTablesRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinLevelParsingTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinLevelParsingTable);
lean_dec_ref(res);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__1);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__2);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__3);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinLevelParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_mkLevelParserAttribute___closed__1 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__1);
l_Lean_Parser_mkLevelParserAttribute___closed__2 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__2);
l_Lean_Parser_mkLevelParserAttribute___closed__3 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__3();
lean_mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__3);
l_Lean_Parser_mkLevelParserAttribute___closed__4 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__4();
lean_mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__4);
l_Lean_Parser_mkLevelParserAttribute___closed__5 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__5();
lean_mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__5);
res = l_Lean_Parser_mkLevelParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_levelParserAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_levelParserAttribute);
lean_dec_ref(res);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12();
lean_mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12);
l_Lean_Parser_Level_paren___closed__1 = _init_l_Lean_Parser_Level_paren___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__1);
l_Lean_Parser_Level_paren___closed__2 = _init_l_Lean_Parser_Level_paren___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__2);
l_Lean_Parser_Level_paren___closed__3 = _init_l_Lean_Parser_Level_paren___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__3);
l_Lean_Parser_Level_paren___closed__4 = _init_l_Lean_Parser_Level_paren___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__4);
l_Lean_Parser_Level_paren___closed__5 = _init_l_Lean_Parser_Level_paren___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__5);
l_Lean_Parser_Level_paren___closed__6 = _init_l_Lean_Parser_Level_paren___closed__6();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__6);
l_Lean_Parser_Level_paren___closed__7 = _init_l_Lean_Parser_Level_paren___closed__7();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__7);
l_Lean_Parser_Level_paren___closed__8 = _init_l_Lean_Parser_Level_paren___closed__8();
lean_mark_persistent(l_Lean_Parser_Level_paren___closed__8);
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean_mark_persistent(l_Lean_Parser_Level_paren);
res = l___regBuiltinParser_Lean_Parser_Level_paren(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_max___elambda__1___closed__1 = _init_l_Lean_Parser_Level_max___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__1);
l_Lean_Parser_Level_max___elambda__1___closed__2 = _init_l_Lean_Parser_Level_max___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__2);
l_Lean_Parser_Level_max___elambda__1___closed__3 = _init_l_Lean_Parser_Level_max___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__3);
l_Lean_Parser_Level_max___elambda__1___closed__4 = _init_l_Lean_Parser_Level_max___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__4);
l_Lean_Parser_Level_max___closed__1 = _init_l_Lean_Parser_Level_max___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_max___closed__1);
l_Lean_Parser_Level_max___closed__2 = _init_l_Lean_Parser_Level_max___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_max___closed__2);
l_Lean_Parser_Level_max___closed__3 = _init_l_Lean_Parser_Level_max___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_max___closed__3);
l_Lean_Parser_Level_max___closed__4 = _init_l_Lean_Parser_Level_max___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_max___closed__4);
l_Lean_Parser_Level_max___closed__5 = _init_l_Lean_Parser_Level_max___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_max___closed__5);
l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
lean_mark_persistent(l_Lean_Parser_Level_max);
res = l___regBuiltinParser_Lean_Parser_Level_max(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_imax___elambda__1___closed__1 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__1);
l_Lean_Parser_Level_imax___elambda__1___closed__2 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__2);
l_Lean_Parser_Level_imax___elambda__1___closed__3 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__3);
l_Lean_Parser_Level_imax___elambda__1___closed__4 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__4);
l_Lean_Parser_Level_imax___closed__1 = _init_l_Lean_Parser_Level_imax___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_imax___closed__1);
l_Lean_Parser_Level_imax___closed__2 = _init_l_Lean_Parser_Level_imax___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_imax___closed__2);
l_Lean_Parser_Level_imax___closed__3 = _init_l_Lean_Parser_Level_imax___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_imax___closed__3);
l_Lean_Parser_Level_imax___closed__4 = _init_l_Lean_Parser_Level_imax___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_imax___closed__4);
l_Lean_Parser_Level_imax___closed__5 = _init_l_Lean_Parser_Level_imax___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_imax___closed__5);
l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
lean_mark_persistent(l_Lean_Parser_Level_imax);
res = l___regBuiltinParser_Lean_Parser_Level_imax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6();
lean_mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6);
l_Lean_Parser_Level_hole___closed__1 = _init_l_Lean_Parser_Level_hole___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_hole___closed__1);
l_Lean_Parser_Level_hole___closed__2 = _init_l_Lean_Parser_Level_hole___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_hole___closed__2);
l_Lean_Parser_Level_hole___closed__3 = _init_l_Lean_Parser_Level_hole___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_hole___closed__3);
l_Lean_Parser_Level_hole___closed__4 = _init_l_Lean_Parser_Level_hole___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_hole___closed__4);
l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
lean_mark_persistent(l_Lean_Parser_Level_hole);
res = l___regBuiltinParser_Lean_Parser_Level_hole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_num___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_num___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_num___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_num___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_num___closed__1 = _init_l_Lean_Parser_Level_num___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_num___closed__1);
l_Lean_Parser_Level_num___closed__2 = _init_l_Lean_Parser_Level_num___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_num___closed__2);
l_Lean_Parser_Level_num___closed__3 = _init_l_Lean_Parser_Level_num___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_num___closed__3);
l_Lean_Parser_Level_num = _init_l_Lean_Parser_Level_num();
lean_mark_persistent(l_Lean_Parser_Level_num);
res = l___regBuiltinParser_Lean_Parser_Level_num(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_ident___closed__1 = _init_l_Lean_Parser_Level_ident___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_ident___closed__1);
l_Lean_Parser_Level_ident___closed__2 = _init_l_Lean_Parser_Level_ident___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_ident___closed__2);
l_Lean_Parser_Level_ident___closed__3 = _init_l_Lean_Parser_Level_ident___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_ident___closed__3);
l_Lean_Parser_Level_ident = _init_l_Lean_Parser_Level_ident();
lean_mark_persistent(l_Lean_Parser_Level_ident);
res = l___regBuiltinParser_Lean_Parser_Level_ident(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_addLit___elambda__1___closed__1 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__1);
l_Lean_Parser_Level_addLit___elambda__1___closed__2 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__2);
l_Lean_Parser_Level_addLit___elambda__1___closed__3 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__3);
l_Lean_Parser_Level_addLit___elambda__1___closed__4 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__4);
l_Lean_Parser_Level_addLit___elambda__1___closed__5 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__5);
l_Lean_Parser_Level_addLit___elambda__1___closed__6 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__6);
l_Lean_Parser_Level_addLit___closed__1 = _init_l_Lean_Parser_Level_addLit___closed__1();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__1);
l_Lean_Parser_Level_addLit___closed__2 = _init_l_Lean_Parser_Level_addLit___closed__2();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__2);
l_Lean_Parser_Level_addLit___closed__3 = _init_l_Lean_Parser_Level_addLit___closed__3();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__3);
l_Lean_Parser_Level_addLit___closed__4 = _init_l_Lean_Parser_Level_addLit___closed__4();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__4);
l_Lean_Parser_Level_addLit___closed__5 = _init_l_Lean_Parser_Level_addLit___closed__5();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__5);
l_Lean_Parser_Level_addLit___closed__6 = _init_l_Lean_Parser_Level_addLit___closed__6();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__6);
l_Lean_Parser_Level_addLit___closed__7 = _init_l_Lean_Parser_Level_addLit___closed__7();
lean_mark_persistent(l_Lean_Parser_Level_addLit___closed__7);
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean_mark_persistent(l_Lean_Parser_Level_addLit);
res = l___regBuiltinParser_Lean_Parser_Level_addLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
