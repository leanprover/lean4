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
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
obj* l_Lean_Parser_Level_paren;
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__2;
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Level_max;
obj* l_Lean_Parser_Level_ident___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__1;
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__1;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_builtinLevelParsingTable;
extern obj* l_Lean_Parser_appPrec;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit;
obj* l___regBuiltinParser_Lean_Parser_Level_num___closed__1;
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_levelParserFn(uint8);
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_Level_max___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__3;
obj* l_Lean_Parser_levelParser(uint8, obj*);
obj* l_Lean_Parser_Level_num;
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj*);
obj* l_Lean_Parser_Level_max___elambda__1___closed__3;
obj* l_Lean_Parser_Level_num___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_hole(obj*);
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__3;
obj* l_Lean_Parser_Level_paren___elambda__1(obj*);
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_levelParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg(obj*, obj*);
extern obj* l_Lean_Parser_manyAux___main___closed__1;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
obj* l_Lean_Parser_levelParser___boxed(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__2;
obj* l_Lean_Parser_Level_num___elambda__1(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_imax(obj*);
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_levelParserFn___rarg___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Level_ident___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Level_ident___elambda__1(obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_numLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l_Lean_Parser_Level_imax;
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj*);
obj* l_Lean_Parser_Level_hole___elambda__1___boxed(obj*);
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_levelParserFn___boxed(obj*);
obj* l_Lean_Parser_Level_addLit___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_hole___elambda__1(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_max(obj*);
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Level_num___elambda__1___rarg(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_ident___closed__1;
obj* l_Lean_Parser_levelParserFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_num(obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___closed__1;
obj* l_Lean_Parser_Level_hole;
obj* l_Lean_Parser_Level_max___elambda__1___boxed(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_paren(obj*);
obj* l_Lean_Parser_Level_ident;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_Level_imax___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_imax___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Level_paren___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_ident(obj*);
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinLevelParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinLevelParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_levelParserFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("universe level");
return x_1;
}
}
obj* l_Lean_Parser_levelParserFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_6 = l_Lean_Parser_builtinLevelParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_levelParserFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParserFn___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_levelParserFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_levelParserFn___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_levelParserFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_levelParserFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_levelParser(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
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
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(")");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(")");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_paren___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinLevelParsingTable;
x_11 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_15 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_16 = l_Lean_Parser_symbolFnAux(x_14, x_15, x_1, x_12);
x_17 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_4);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_13);
lean::dec(x_1);
x_19 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_4);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_8);
lean::dec(x_1);
x_21 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_22 = l_Lean_Parser_ParserState_mkNode(x_7, x_21, x_4);
return x_22;
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
obj* _init_l_Lean_Parser_Level_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("(");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::box(0);
x_10 = lean::mk_string(")");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolInfo(x_11, x_9);
x_13 = l_Lean_Parser_andthenInfo(x_8, x_12);
x_14 = l_Lean_Parser_andthenInfo(x_5, x_13);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren___elambda__1___boxed), 1, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
x_3 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__5;
x_4 = l_Lean_Parser_Level_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_8 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_9 = l_Lean_Parser_builtinLevelParsingTable;
x_10 = l_Lean_Parser_appPrec;
lean::inc(x_3);
x_11 = l_Lean_Parser_runBuiltinParserUnsafe(x_8, x_9, x_10, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_7, x_13);
lean::dec(x_13);
lean::dec(x_7);
if (x_14 == 0)
{
x_4 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_3);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_3);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_6, x_7);
lean::dec(x_6);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("max");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("max");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_max___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("max");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_max___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinLevelParsingTable;
x_14 = l_Lean_Parser_appPrec;
lean::inc(x_2);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_2, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = 0;
x_18 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_17, x_1, x_2, x_15);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_11);
x_21 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_5);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_16);
lean::dec(x_2);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_15, x_23, x_11);
x_25 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_5);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_9);
lean::dec(x_2);
x_27 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_28 = l_Lean_Parser_ParserState_mkNode(x_8, x_27, x_5);
return x_28;
}
}
}
obj* _init_l_Lean_Parser_Level_max() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("max");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_max___elambda__1___boxed), 3, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
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
x_3 = l_Lean_Parser_Level_max___elambda__1___closed__3;
x_4 = l_Lean_Parser_Level_max;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("imax");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("imax");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_imax___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("imax");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_imax___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_7 = l_Lean_Parser_Level_imax___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinLevelParsingTable;
x_14 = l_Lean_Parser_appPrec;
lean::inc(x_2);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_2, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = 0;
x_18 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Level_max___elambda__1___spec__1(x_17, x_1, x_2, x_15);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_11);
x_21 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_5);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_16);
lean::dec(x_2);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_15, x_23, x_11);
x_25 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_5);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_9);
lean::dec(x_2);
x_27 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_28 = l_Lean_Parser_ParserState_mkNode(x_8, x_27, x_5);
return x_28;
}
}
}
obj* _init_l_Lean_Parser_Level_imax() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("imax");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_imax___elambda__1___boxed), 3, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
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
x_3 = l_Lean_Parser_Level_imax___elambda__1___closed__3;
x_4 = l_Lean_Parser_Level_imax;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("_");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("_");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_hole___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
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
obj* _init_l_Lean_Parser_Level_hole() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_hole___elambda__1___boxed), 1, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
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
x_3 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Level_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_Level_num___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_numLitFn___rarg(x_1, x_2);
return x_3;
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
obj* _init_l_Lean_Parser_Level_num() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_string("numLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_num___elambda__1___boxed), 1, 0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
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
obj* _init_l___regBuiltinParser_Lean_Parser_Level_num___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("num");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_num(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_num___closed__1;
x_4 = l_Lean_Parser_Level_num;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_Level_ident___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_identFn___rarg(x_1, x_2);
return x_3;
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
obj* _init_l_Lean_Parser_Level_ident() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_ident___elambda__1___boxed), 1, 0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
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
obj* _init_l___regBuiltinParser_Lean_Parser_Level_ident___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("ident");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_ident(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_ident___closed__1;
x_4 = l_Lean_Parser_Level_ident;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("+");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("+");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("addLit");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_addLit___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_3);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = l_Lean_Parser_Level_addLit___elambda__1___closed__1;
x_9 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
lean::inc(x_2);
x_10 = l_Lean_Parser_symbolFnAux(x_8, x_9, x_2, x_6);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = l_Lean_Parser_numLitFn___rarg(x_2, x_10);
x_13 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_5);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_11);
lean::dec(x_2);
x_15 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_10, x_15, x_5);
return x_16;
}
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_7);
lean::dec(x_2);
x_17 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_5);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_Level_addLit() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::mk_nat_obj(65u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("+");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::mk_string("numLit");
x_7 = l_Lean_Parser_mkAtomicInfo(x_6);
x_8 = l_Lean_Parser_andthenInfo(x_5, x_7);
x_9 = l_Lean_Parser_epsilonInfo;
x_10 = l_Lean_Parser_andthenInfo(x_9, x_8);
x_11 = l_Lean_Parser_nodeInfo(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit___elambda__1), 3, 0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l_Lean_Parser_Level_addLit___elambda__1___closed__3;
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
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinLevelParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinLevelParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinLevelParsingTable"), l_Lean_Parser_builtinLevelParsingTable);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__1);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinLevelParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_levelParserFn___rarg___closed__1 = _init_l_Lean_Parser_levelParserFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_levelParserFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "levelParserFn"), 1, l_Lean_Parser_levelParserFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "levelParser"), 2, l_Lean_Parser_levelParser___boxed);
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
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean::mark_persistent(l_Lean_Parser_Level_paren);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "paren"), l_Lean_Parser_Level_paren);
w = l___regBuiltinParser_Lean_Parser_Level_paren(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_max___elambda__1___closed__1 = _init_l_Lean_Parser_Level_max___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__1);
l_Lean_Parser_Level_max___elambda__1___closed__2 = _init_l_Lean_Parser_Level_max___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__2);
l_Lean_Parser_Level_max___elambda__1___closed__3 = _init_l_Lean_Parser_Level_max___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_max___elambda__1___closed__3);
l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
lean::mark_persistent(l_Lean_Parser_Level_max);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "max"), l_Lean_Parser_Level_max);
w = l___regBuiltinParser_Lean_Parser_Level_max(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_imax___elambda__1___closed__1 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__1);
l_Lean_Parser_Level_imax___elambda__1___closed__2 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__2);
l_Lean_Parser_Level_imax___elambda__1___closed__3 = _init_l_Lean_Parser_Level_imax___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_imax___elambda__1___closed__3);
l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
lean::mark_persistent(l_Lean_Parser_Level_imax);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "imax"), l_Lean_Parser_Level_imax);
w = l___regBuiltinParser_Lean_Parser_Level_imax(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2);
l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_hole___elambda__1___rarg___closed__3);
l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
lean::mark_persistent(l_Lean_Parser_Level_hole);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "hole"), l_Lean_Parser_Level_hole);
w = l___regBuiltinParser_Lean_Parser_Level_hole(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_num = _init_l_Lean_Parser_Level_num();
lean::mark_persistent(l_Lean_Parser_Level_num);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "num"), l_Lean_Parser_Level_num);
l___regBuiltinParser_Lean_Parser_Level_num___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_num___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_num___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_num(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_ident = _init_l_Lean_Parser_Level_ident();
lean::mark_persistent(l_Lean_Parser_Level_ident);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "ident"), l_Lean_Parser_Level_ident);
l___regBuiltinParser_Lean_Parser_Level_ident___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_ident___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_ident___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_ident(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_addLit___elambda__1___closed__1 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__1);
l_Lean_Parser_Level_addLit___elambda__1___closed__2 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__2);
l_Lean_Parser_Level_addLit___elambda__1___closed__3 = _init_l_Lean_Parser_Level_addLit___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_addLit___elambda__1___closed__3);
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean::mark_persistent(l_Lean_Parser_Level_addLit);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "addLit"), l_Lean_Parser_Level_addLit);
w = l___regBuiltinParser_Lean_Parser_Level_addLit(w);
if (io_result_is_error(w)) return w;
return w;
}
