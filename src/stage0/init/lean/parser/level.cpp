// Lean compiler output
// Module: init.lean.parser.level
// Imports: init.lean.parser.parser
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l_Lean_Parser_Level_max___closed__2;
obj* l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__5;
obj* l_Lean_Parser_mkLevelParserAttribute___closed__5;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_imax___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__3;
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkLevelParserAttribute(obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
obj* l_Lean_Parser_Level_paren;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
obj* l_Lean_Parser_Level_imax___closed__2;
obj* l_Lean_Parser_Level_hole___closed__4;
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__2;
obj* l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
extern obj* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
obj* l_Lean_Parser_Level_max;
obj* l_Lean_Parser_ParserAttribute_runParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_ident___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__1;
extern obj* l_Lean_LevelToFormat_Result_format___main___closed__3;
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__1;
obj* l_Lean_Parser_Level_num___closed__3;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_mkLevelParserAttribute___closed__1;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
obj* l_Lean_Parser_ParserState_mkUnexpectedError(obj*, obj*);
obj* l_Lean_Parser_Level_paren___closed__5;
obj* l_Lean_Parser_Level_addLit___closed__6;
obj* l_Lean_Parser_Level_hole___closed__2;
extern obj* l_Lean_Name_appendIndexAfter___closed__1;
extern obj* l_Lean_Parser_appPrec;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit;
obj* l_Lean_Parser_Level_paren___closed__3;
extern obj* l_Lean_LevelToFormat_Result_format___main___closed__5;
obj* l_Lean_Parser_registerParserAttribute(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_max___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__3;
extern obj* l_Lean_LevelToFormat_Result_format___main___closed__1;
obj* l_Lean_Parser_levelParser(uint8, obj*);
obj* l_Lean_Parser_Level_num;
obj* l_Lean_Parser_Level_paren___closed__4;
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__3;
obj* l_Lean_Parser_Level_paren___closed__1;
obj* l_Lean_Parser_Level_paren___closed__6;
obj* l_Lean_Parser_Level_num___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_hole(obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__3;
obj* l_Lean_Parser_Level_num___closed__1;
obj* l_Lean_Parser_Level_paren___elambda__1(obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_max___closed__4;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_max___closed__1;
obj* l_Lean_Parser_Level_addLit___closed__5;
obj* l_Lean_Parser_Level_ident___closed__3;
obj* l_Lean_Parser_levelParser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_levelParser___lambda__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_manyAux___main___closed__1;
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
obj* lean_string_append(obj*, obj*);
obj* l_Lean_Parser_symbolOrIdentFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
obj* l_Lean_Parser_levelParser___boxed(obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_Lean_Parser_Level_imax___elambda__1___closed__4;
obj* l_Lean_Parser_tokenFn(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_levelParserAttribute;
obj* l_Lean_Parser_mkLevelParserAttribute___closed__2;
obj* l_Lean_Parser_Level_paren___closed__7;
obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__2;
obj* l_Lean_Parser_Level_num___elambda__1(obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__4;
obj* l___regBuiltinParser_Lean_Parser_Level_imax(obj*);
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_num___closed__2;
obj* l_Lean_Parser_Level_max___elambda__1___closed__4;
obj* l_Lean_Parser_Level_ident___closed__1;
uint8 lean_nat_dec_eq(obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_Lean_Parser_Level_ident___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
extern obj* l_Lean_Parser_ident___closed__1;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Level_ident___elambda__1(obj*);
obj* l_Lean_Parser_Level_ident___closed__2;
uint8 lean_string_dec_eq(obj*, obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_numLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_paren___closed__2;
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7;
obj* l_Lean_Parser_Level_imax;
obj* l_Lean_Parser_Level_imax___closed__5;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4;
extern obj* l_Lean_Parser_numLit___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj*);
obj* l_Lean_Parser_Level_imax___closed__4;
obj* l_Lean_Parser_Level_hole___elambda__1___boxed(obj*);
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_Level_imax___closed__3;
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__4;
obj* l_Lean_Parser_Level_addLit___closed__1;
obj* l_Lean_Parser_Level_addLit___closed__7;
obj* l_Lean_Parser_Level_addLit___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_hole___closed__1;
obj* l_Lean_Parser_Level_hole___elambda__1(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_max(obj*);
obj* l_Lean_Parser_symbolOrIdentInfo(obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10;
obj* l_Lean_Parser_nodeInfo(obj*, obj*);
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__6;
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_mkLevelParserAttribute___closed__3;
obj* l_Lean_Parser_Level_max___closed__5;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Level_num___elambda__1___rarg(obj*, obj*);
extern obj* l_Lean_Parser_ParserAttribute_inhabited___closed__4;
obj* l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8, obj*, obj*, obj*);
extern obj* l_Lean_Parser_symbolOrIdentInfo___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Level_num(obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__1;
obj* l_Lean_Parser_Level_hole;
obj* l_Lean_Parser_Level_max___elambda__1___boxed(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_paren(obj*);
obj* l_Lean_Parser_Level_addLit___closed__3;
obj* l_Lean_Parser_Level_ident;
obj* l_Lean_Parser_Level_addLit___closed__2;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_Level_paren___closed__8;
obj* l_Lean_Parser_Level_imax___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_hole___closed__3;
obj* l_Lean_Parser_Level_imax___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkErrorsAt(obj*, obj*, obj*);
obj* l_Lean_Parser_mkLevelParserAttribute___closed__4;
obj* l_Lean_Parser_Level_max___closed__3;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Level_paren___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Level_addLit___closed__4;
obj* l___regBuiltinParser_Lean_Parser_Level_ident(obj*);
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinLevelParser");
return x_1;
}
}
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinLevelParsingTable");
return x_1;
}
}
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_mkLevelParserAttribute___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("levelParser");
return x_1;
}
}
obj* _init_l_Lean_Parser_mkLevelParserAttribute___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_mkLevelParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_mkLevelParserAttribute___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_builtinLevelParsingTable;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_mkLevelParserAttribute___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("level");
return x_1;
}
}
obj* _init_l_Lean_Parser_mkLevelParserAttribute___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("universe level parser");
return x_1;
}
}
obj* l_Lean_Parser_mkLevelParserAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_Lean_Parser_mkLevelParserAttribute___closed__2;
x_3 = l_Lean_Parser_mkLevelParserAttribute___closed__4;
x_4 = l_Lean_Parser_mkLevelParserAttribute___closed__5;
x_5 = l_Lean_Parser_mkLevelParserAttribute___closed__3;
x_6 = l_Lean_Parser_registerParserAttribute(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
obj* l_Lean_Parser_levelParser___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_levelParserAttribute;
x_6 = l_Lean_Parser_ParserAttribute_runParser(x_5, x_1, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_levelParser(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___lambda__1___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_levelParser___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_levelParser___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_levelParser___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_levelParser(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Level");
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("paren");
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Level_paren___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_38; obj* x_39; obj* x_40; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean_array_get_size(x_3);
lean::dec(x_3);
x_38 = lean::cnstr_get(x_2, 1);
lean::inc(x_38);
lean::inc(x_1);
x_39 = l_Lean_Parser_tokenFn(x_1, x_2);
x_40 = lean::cnstr_get(x_39, 3);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_42 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_41);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 2)
{
obj* x_43; obj* x_44; uint8 x_45; 
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_44 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_45 = lean_string_dec_eq(x_43, x_44);
lean::dec(x_43);
if (x_45 == 0)
{
obj* x_46; obj* x_47; 
x_46 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
x_47 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_46, x_38);
x_5 = x_47;
goto block_37;
}
else
{
lean::dec(x_38);
x_5 = x_39;
goto block_37;
}
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_42);
x_48 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_48, x_38);
x_5 = x_49;
goto block_37;
}
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_40);
x_50 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12;
x_51 = l_Lean_Parser_ParserState_mkErrorsAt(x_39, x_50, x_38);
x_5 = x_51;
goto block_37;
}
block_37:
{
obj* x_6; 
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_levelParserAttribute;
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_9 = l_Lean_Parser_ParserAttribute_runParser(x_7, x_8, x_1, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_12 = l_Lean_Parser_tokenFn(x_1, x_9);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_14);
lean::dec(x_14);
if (lean::obj_tag(x_15) == 2)
{
obj* x_16; obj* x_17; uint8 x_18; 
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_18 = lean_string_dec_eq(x_16, x_17);
lean::dec(x_16);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_19, x_11);
x_21 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_11);
x_23 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_24 = l_Lean_Parser_ParserState_mkNode(x_12, x_23, x_4);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_15);
x_25 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_26 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_25, x_11);
x_27 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_4);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_29 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9;
x_30 = l_Lean_Parser_ParserState_mkErrorsAt(x_12, x_29, x_11);
x_31 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_4);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_10);
lean::dec(x_1);
x_33 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_34 = l_Lean_Parser_ParserState_mkNode(x_9, x_33, x_4);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_6);
lean::dec(x_1);
x_35 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_36 = l_Lean_Parser_ParserState_mkNode(x_5, x_35, x_4);
return x_36;
}
}
}
}
obj* l_Lean_Parser_Level_paren___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Level_paren___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___closed__2;
x_2 = l_Lean_Parser_Level_paren___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_2 = l_Lean_Parser_Level_paren___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_paren___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___closed__6;
x_2 = l_Lean_Parser_Level_paren___closed__7;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_paren___closed__8;
return x_1;
}
}
obj* l_Lean_Parser_Level_paren___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_paren___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_paren(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_4 = l_Lean_Parser_Level_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean_array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_8 = l_Lean_Parser_levelParserAttribute;
x_9 = l_Lean_Parser_appPrec;
lean::inc(x_3);
x_10 = l_Lean_Parser_ParserAttribute_runParser(x_8, x_9, x_3, x_4);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; uint8 x_13; 
lean::dec(x_6);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_13 = lean_nat_dec_eq(x_7, x_12);
lean::dec(x_12);
lean::dec(x_7);
if (x_13 == 0)
{
x_4 = x_10;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_3);
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_10, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_18 = lean_nat_dec_eq(x_7, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
lean::dec(x_7);
lean::dec(x_6);
return x_10;
}
else
{
obj* x_19; 
x_19 = l_Lean_Parser_ParserState_restore(x_10, x_6, x_7);
lean::dec(x_6);
return x_19;
}
}
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_LevelToFormat_Result_format___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_max___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean_array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__4;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolOrIdentFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean_array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_levelParserAttribute;
x_13 = l_Lean_Parser_appPrec;
lean::inc(x_2);
x_14 = l_Lean_Parser_ParserAttribute_runParser(x_12, x_13, x_2, x_8);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
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
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_15);
lean::dec(x_2);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_11);
x_24 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_2);
x_26 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_8, x_26, x_5);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_Level_max___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_max___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_max___closed__1;
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_max___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_2 = l_Lean_Parser_Level_max___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_max___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_max___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_max___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_max___closed__3;
x_2 = l_Lean_Parser_Level_max___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_max() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_max___closed__5;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Level_max___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Level_max___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_max(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_4 = l_Lean_Parser_Level_max;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_LevelToFormat_Result_format___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_imax___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean_array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_7 = l_Lean_Parser_Level_imax___elambda__1___closed__4;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolOrIdentFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean_array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_levelParserAttribute;
x_13 = l_Lean_Parser_appPrec;
lean::inc(x_2);
x_14 = l_Lean_Parser_ParserAttribute_runParser(x_12, x_13, x_2, x_8);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
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
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_15);
lean::dec(x_2);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_11);
x_24 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_2);
x_26 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_8, x_26, x_5);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_Level_imax___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_imax___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_imax___closed__1;
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_imax___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_2 = l_Lean_Parser_Level_imax___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_imax___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_imax___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_imax___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_imax___closed__3;
x_2 = l_Lean_Parser_Level_imax___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_imax() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_imax___closed__5;
return x_1;
}
}
obj* l_Lean_Parser_Level_imax___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Level_imax___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_imax(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_4 = l_Lean_Parser_Level_imax;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("hole");
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Name_appendIndexAfter___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Level_hole___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean_array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 2)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_12 = lean_string_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_13, x_5);
x_15 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_5);
x_17 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_4);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_9);
x_19 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_19, x_5);
x_21 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_7);
x_23 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_23, x_5);
x_25 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
}
}
obj* l_Lean_Parser_Level_hole___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_hole___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_hole___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_hole___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_hole___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_hole___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_hole___closed__2;
x_2 = l_Lean_Parser_Level_hole___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_hole() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_hole___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Level_hole___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_hole___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_hole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_4 = l_Lean_Parser_Level_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("num");
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_num___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean_array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_numLitFn___rarg(x_1, x_2);
x_6 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_ParserState_mkNode(x_5, x_6, x_4);
return x_7;
}
}
obj* l_Lean_Parser_Level_num___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_num___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_num___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_numLit___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_num___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_num___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_num___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_num___closed__1;
x_2 = l_Lean_Parser_Level_num___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_num() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_num___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_Level_num___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_num___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_num(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_4 = l_Lean_Parser_Level_num;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_ident___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean_array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_6 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_7 = l_Lean_Parser_ParserState_mkNode(x_5, x_6, x_4);
return x_7;
}
}
obj* l_Lean_Parser_Level_ident___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_ident___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_ident___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_2 = l_Lean_Parser_ident___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_ident___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_ident___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_ident___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_ident___closed__1;
x_2 = l_Lean_Parser_Level_ident___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_ident() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_ident___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_Level_ident___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_ident___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_ident(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_4 = l_Lean_Parser_Level_ident;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("addLit");
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_LevelToFormat_Result_format___main___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_addLit___elambda__1___closed__5;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Level_addLit___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_14; obj* x_15; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean_array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_3);
x_14 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_15 = lean::cnstr_get(x_3, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::dec(x_3);
lean::inc(x_2);
x_17 = l_Lean_Parser_tokenFn(x_2, x_14);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_20 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_19);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 2)
{
obj* x_21; obj* x_22; uint8 x_23; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_23 = lean_string_dec_eq(x_21, x_22);
lean::dec(x_21);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_24, x_16);
x_6 = x_25;
goto block_13;
}
else
{
lean::dec(x_16);
x_6 = x_17;
goto block_13;
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_20);
x_26 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_26, x_16);
x_6 = x_27;
goto block_13;
}
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_18);
x_28 = l_Lean_Parser_Level_addLit___elambda__1___closed__6;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_17, x_28, x_16);
x_6 = x_29;
goto block_13;
}
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_2);
x_30 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_14, x_30, x_5);
return x_31;
}
block_13:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = l_Lean_Parser_numLitFn___rarg(x_2, x_6);
x_9 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_7);
lean::dec(x_2);
x_11 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_6, x_11, x_5);
return x_12;
}
}
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(65u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_2 = l_Lean_Parser_Level_addLit___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_addLit___closed__2;
x_2 = l_Lean_Parser_numLit___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_Level_addLit___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_2 = l_Lean_Parser_Level_addLit___closed__4;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit___elambda__1), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_addLit___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_addLit___closed__5;
x_2 = l_Lean_Parser_Level_addLit___closed__6;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_addLit___closed__7;
return x_1;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_4 = l_Lean_Parser_Level_addLit;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_parser_parser(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_level(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (lean::io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_builtinLevelParsingTable = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinLevelParsingTable);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__1);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__2);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__3();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__3);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__4();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__4);
w = l_Lean_Parser_regBuiltinLevelParserAttr(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_mkLevelParserAttribute___closed__1 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__1();
lean::mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__1);
l_Lean_Parser_mkLevelParserAttribute___closed__2 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__2();
lean::mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__2);
l_Lean_Parser_mkLevelParserAttribute___closed__3 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__3();
lean::mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__3);
l_Lean_Parser_mkLevelParserAttribute___closed__4 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__4();
lean::mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__4);
l_Lean_Parser_mkLevelParserAttribute___closed__5 = _init_l_Lean_Parser_mkLevelParserAttribute___closed__5();
lean::mark_persistent(l_Lean_Parser_mkLevelParserAttribute___closed__5);
w = l_Lean_Parser_mkLevelParserAttribute(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_levelParserAttribute = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_levelParserAttribute);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__6);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__7);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__8);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__9);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__10);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__11);
l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12 = _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12();
lean::mark_persistent(l_Lean_Parser_Level_paren___elambda__1___rarg___closed__12);
l_Lean_Parser_Level_paren___closed__1 = _init_l_Lean_Parser_Level_paren___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__1);
l_Lean_Parser_Level_paren___closed__2 = _init_l_Lean_Parser_Level_paren___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__2);
l_Lean_Parser_Level_paren___closed__3 = _init_l_Lean_Parser_Level_paren___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__3);
l_Lean_Parser_Level_paren___closed__4 = _init_l_Lean_Parser_Level_paren___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__4);
l_Lean_Parser_Level_paren___closed__5 = _init_l_Lean_Parser_Level_paren___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__5);
l_Lean_Parser_Level_paren___closed__6 = _init_l_Lean_Parser_Level_paren___closed__6();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__6);
l_Lean_Parser_Level_paren___closed__7 = _init_l_Lean_Parser_Level_paren___closed__7();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__7);
l_Lean_Parser_Level_paren___closed__8 = _init_l_Lean_Parser_Level_paren___closed__8();
lean::mark_persistent(l_Lean_Parser_Level_paren___closed__8);
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean::mark_persistent(l_Lean_Parser_Level_paren);
w = l___regBuiltinParser_Lean_Parser_Level_paren(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_max___elambda__1___closed__1 = _init_l_Lean_Parser_Level_max___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__1);
l_Lean_Parser_Level_max___elambda__1___closed__2 = _init_l_Lean_Parser_Level_max___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__2);
l_Lean_Parser_Level_max___elambda__1___closed__3 = _init_l_Lean_Parser_Level_max___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__3);
l_Lean_Parser_Level_max___elambda__1___closed__4 = _init_l_Lean_Parser_Level_max___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__4);
l_Lean_Parser_Level_max___closed__1 = _init_l_Lean_Parser_Level_max___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_max___closed__1);
l_Lean_Parser_Level_max___closed__2 = _init_l_Lean_Parser_Level_max___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_max___closed__2);
l_Lean_Parser_Level_max___closed__3 = _init_l_Lean_Parser_Level_max___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_max___closed__3);
l_Lean_Parser_Level_max___closed__4 = _init_l_Lean_Parser_Level_max___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_max___closed__4);
l_Lean_Parser_Level_max___closed__5 = _init_l_Lean_Parser_Level_max___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_max___closed__5);
l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
lean::mark_persistent(l_Lean_Parser_Level_max);
w = l___regBuiltinParser_Lean_Parser_Level_max(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_imax___elambda__1___closed__1 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__1);
l_Lean_Parser_Level_imax___elambda__1___closed__2 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__2);
l_Lean_Parser_Level_imax___elambda__1___closed__3 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__3);
l_Lean_Parser_Level_imax___elambda__1___closed__4 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__4);
l_Lean_Parser_Level_imax___closed__1 = _init_l_Lean_Parser_Level_imax___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_imax___closed__1);
l_Lean_Parser_Level_imax___closed__2 = _init_l_Lean_Parser_Level_imax___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_imax___closed__2);
l_Lean_Parser_Level_imax___closed__3 = _init_l_Lean_Parser_Level_imax___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_imax___closed__3);
l_Lean_Parser_Level_imax___closed__4 = _init_l_Lean_Parser_Level_imax___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_imax___closed__4);
l_Lean_Parser_Level_imax___closed__5 = _init_l_Lean_Parser_Level_imax___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_imax___closed__5);
l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
lean::mark_persistent(l_Lean_Parser_Level_imax);
w = l___regBuiltinParser_Lean_Parser_Level_imax(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__4);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__5);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__6);
l_Lean_Parser_Level_hole___closed__1 = _init_l_Lean_Parser_Level_hole___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_hole___closed__1);
l_Lean_Parser_Level_hole___closed__2 = _init_l_Lean_Parser_Level_hole___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_hole___closed__2);
l_Lean_Parser_Level_hole___closed__3 = _init_l_Lean_Parser_Level_hole___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_hole___closed__3);
l_Lean_Parser_Level_hole___closed__4 = _init_l_Lean_Parser_Level_hole___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_hole___closed__4);
l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
lean::mark_persistent(l_Lean_Parser_Level_hole);
w = l___regBuiltinParser_Lean_Parser_Level_hole(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_num___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_num___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_num___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_num___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_num___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_num___closed__1 = _init_l_Lean_Parser_Level_num___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_num___closed__1);
l_Lean_Parser_Level_num___closed__2 = _init_l_Lean_Parser_Level_num___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_num___closed__2);
l_Lean_Parser_Level_num___closed__3 = _init_l_Lean_Parser_Level_num___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_num___closed__3);
l_Lean_Parser_Level_num = _init_l_Lean_Parser_Level_num();
lean::mark_persistent(l_Lean_Parser_Level_num);
w = l___regBuiltinParser_Lean_Parser_Level_num(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_ident___closed__1 = _init_l_Lean_Parser_Level_ident___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_ident___closed__1);
l_Lean_Parser_Level_ident___closed__2 = _init_l_Lean_Parser_Level_ident___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_ident___closed__2);
l_Lean_Parser_Level_ident___closed__3 = _init_l_Lean_Parser_Level_ident___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_ident___closed__3);
l_Lean_Parser_Level_ident = _init_l_Lean_Parser_Level_ident();
lean::mark_persistent(l_Lean_Parser_Level_ident);
w = l___regBuiltinParser_Lean_Parser_Level_ident(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Parser_Level_addLit___elambda__1___closed__1 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__1);
l_Lean_Parser_Level_addLit___elambda__1___closed__2 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__2);
l_Lean_Parser_Level_addLit___elambda__1___closed__3 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__3);
l_Lean_Parser_Level_addLit___elambda__1___closed__4 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__4);
l_Lean_Parser_Level_addLit___elambda__1___closed__5 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__5);
l_Lean_Parser_Level_addLit___elambda__1___closed__6 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__6);
l_Lean_Parser_Level_addLit___closed__1 = _init_l_Lean_Parser_Level_addLit___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__1);
l_Lean_Parser_Level_addLit___closed__2 = _init_l_Lean_Parser_Level_addLit___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__2);
l_Lean_Parser_Level_addLit___closed__3 = _init_l_Lean_Parser_Level_addLit___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__3);
l_Lean_Parser_Level_addLit___closed__4 = _init_l_Lean_Parser_Level_addLit___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__4);
l_Lean_Parser_Level_addLit___closed__5 = _init_l_Lean_Parser_Level_addLit___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__5);
l_Lean_Parser_Level_addLit___closed__6 = _init_l_Lean_Parser_Level_addLit___closed__6();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__6);
l_Lean_Parser_Level_addLit___closed__7 = _init_l_Lean_Parser_Level_addLit___closed__7();
lean::mark_persistent(l_Lean_Parser_Level_addLit___closed__7);
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean::mark_persistent(l_Lean_Parser_Level_addLit);
w = l___regBuiltinParser_Lean_Parser_Level_addLit(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
}
