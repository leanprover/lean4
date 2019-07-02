// Lean compiler output
// Module: init.lean.parser.term
// Imports: init.lean.parser.parser init.lean.parser.level
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
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_termParser(uint8, obj*);
obj* l_Lean_Parser_orelseFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_strLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_num;
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1;
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1(uint8);
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Term_parenSpecial;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_Term_hole;
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
extern obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ident(obj*);
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_levelParser(uint8, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2;
obj* l_Lean_Parser_Term_str;
obj* l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_paren___closed__1;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l___regBuiltinParser_Lean_Parser_Term_ident___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_cdot;
obj* l_Lean_Parser_termParser___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_paren;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Term_sort;
obj* l_Lean_Parser_Term_ident;
obj* l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
extern obj* l_Lean_Parser_maxPrec;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___rarg(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj*);
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj*);
obj* l_Lean_Parser_Term_type;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_levelParser___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepByInfo(obj*, obj*);
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* l_Lean_Parser_Term_app;
obj* l___regBuiltinParser_Lean_Parser_Term_sort___closed__1;
obj* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinTermParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinTermParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_termParser___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term");
return x_1;
}
}
obj* l_Lean_Parser_termParser___elambda__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_termParser___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_builtinTermParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_termParser___elambda__1(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_termParser(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_termParser___elambda__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_termParser___elambda__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_termParser___elambda__1___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_termParser___elambda__1(x_2);
return x_3;
}
}
obj* l_Lean_Parser_termParser___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_termParser(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(", ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(", ");
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
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_levelParser___elambda__1___rarg___closed__1;
x_12 = l_Lean_Parser_builtinLevelParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1;
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2;
lean::inc(x_6);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_6, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_18);
lean::dec(x_17);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_21;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_17, x_18);
lean::dec(x_17);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_3);
return x_26;
}
}
else
{
lean::dec(x_15);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_9);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_14, x_9, x_10);
lean::dec(x_9);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_3);
return x_33;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 0;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_ident() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("ident");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_mkAtomicInfo(x_8);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::box(0);
x_15 = lean::mk_string(".{");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_17 = l_Lean_Parser_symbolInfo(x_16, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_18, 0, x_16);
x_19 = lean::mk_nat_obj(0u);
x_20 = l_Lean_Parser_levelParser(x_11, x_19);
x_21 = lean::mk_string(", ");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_14);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_25 = l_Lean_Parser_sepBy1Info(x_24, x_23);
x_26 = 0;
x_27 = lean::box(x_11);
x_28 = lean::box(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1___boxed), 5, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::mk_string("}");
x_31 = l_String_trim(x_30);
lean::dec(x_30);
lean::inc(x_31);
x_32 = l_Lean_Parser_symbolInfo(x_31, x_14);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_33, 0, x_31);
x_34 = l_Lean_Parser_andthenInfo(x_25, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_29);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_17, x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_18);
lean::closure_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_noFirstTokenInfo(x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_39, 0, x_37);
x_40 = l_Lean_Parser_andthenInfo(x_10, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_13);
lean::closure_set(x_41, 1, x_39);
x_42 = l_Lean_Parser_nodeInfo(x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_9);
lean::closure_set(x_43, 1, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_ident___spec__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_ident___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_ident___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("ident");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_ident(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_ident___closed__1;
x_4 = l_Lean_Parser_Term_ident;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_num() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("numLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numLitFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_num___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("num");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
x_4 = l_Lean_Parser_Term_num;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_str() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("strLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_strLitFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_str___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("str");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
x_4 = l_Lean_Parser_Term_str;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_type() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("type");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("Type");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_type___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("type");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
x_4 = l_Lean_Parser_Term_type;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sort() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sort");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("Sort");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_sort___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sort");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_sort___closed__1;
x_4 = l_Lean_Parser_Term_sort;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_hole() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("_");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_hole___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
x_4 = l_Lean_Parser_Term_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_cdot() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("cdot");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("\xb7");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("cdot");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1;
x_4 = l_Lean_Parser_Term_cdot;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_termParser___elambda__1___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1;
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2;
lean::inc(x_6);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_6, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_18);
lean::dec(x_17);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_21;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_17, x_18);
lean::dec(x_17);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_3);
return x_26;
}
}
else
{
lean::dec(x_15);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_9);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_14, x_9, x_10);
lean::dec(x_9);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_3);
return x_33;
}
}
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 1;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_parenSpecial() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::box(0);
x_2 = lean::mk_string(", ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
lean::inc(x_3);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = 0;
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Lean_Parser_termParser(x_6, x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
lean::inc(x_4);
lean::inc(x_9);
x_10 = l_Lean_Parser_sepByInfo(x_9, x_4);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_11, 0, x_7);
x_12 = 0;
x_13 = lean::box(x_6);
x_14 = lean::box(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1___boxed), 5, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_andthenInfo(x_4, x_10);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_5);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::mk_string(" : ");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolInfo(x_19, x_1);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_21, 0, x_19);
x_22 = l_Lean_Parser_andthenInfo(x_20, x_9);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_11);
x_24 = l_Lean_Parser_orelseInfo(x_16, x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_17);
lean::closure_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_noFirstTokenInfo(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_27, 0, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_parenSpecial___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_parenSpecial___spec__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l_Lean_Parser_Term_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("(");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = 0;
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Lean_Parser_termParser(x_16, x_17);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::box(0);
x_21 = lean::mk_string(", ");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
lean::inc(x_23);
lean::inc(x_19);
x_25 = l_Lean_Parser_sepByInfo(x_19, x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_26, 0, x_17);
x_27 = 0;
x_28 = lean::box(x_16);
x_29 = lean::box(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByFn___at_Lean_Parser_Term_parenSpecial___spec__1___boxed), 5, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_andthenInfo(x_23, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_32, 0, x_24);
lean::closure_set(x_32, 1, x_30);
x_33 = lean::mk_string(" : ");
x_34 = l_String_trim(x_33);
lean::dec(x_33);
lean::inc(x_34);
x_35 = l_Lean_Parser_symbolInfo(x_34, x_20);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_36, 0, x_34);
lean::inc(x_19);
x_37 = l_Lean_Parser_andthenInfo(x_35, x_19);
lean::inc(x_26);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_36);
lean::closure_set(x_38, 1, x_26);
x_39 = l_Lean_Parser_orelseInfo(x_31, x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_40, 0, x_32);
lean::closure_set(x_40, 1, x_38);
x_41 = l_Lean_Parser_noFirstTokenInfo(x_39);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_42, 0, x_40);
x_43 = l_Lean_Parser_andthenInfo(x_19, x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_44, 0, x_26);
lean::closure_set(x_44, 1, x_42);
x_45 = l_Lean_Parser_noFirstTokenInfo(x_43);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_46, 0, x_44);
x_47 = lean::mk_string(")");
x_48 = l_String_trim(x_47);
lean::dec(x_47);
lean::inc(x_48);
x_49 = l_Lean_Parser_symbolInfo(x_48, x_20);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_50, 0, x_48);
x_51 = l_Lean_Parser_andthenInfo(x_45, x_49);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_52, 0, x_46);
lean::closure_set(x_52, 1, x_50);
x_53 = l_Lean_Parser_andthenInfo(x_14, x_51);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_54, 0, x_15);
lean::closure_set(x_54, 1, x_52);
x_55 = l_Lean_Parser_nodeInfo(x_53);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_56, 0, x_9);
lean::closure_set(x_56, 1, x_54);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_paren___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_paren___closed__1;
x_4 = l_Lean_Parser_Term_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_app() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("app");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = 1;
x_11 = l_Lean_Parser_maxPrec;
x_12 = l_Lean_Parser_termParser(x_10, x_11);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
x_14 = l_Lean_Parser_epsilonInfo;
x_15 = l_Lean_Parser_andthenInfo(x_14, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_16, 0, x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_18, 0, x_17);
lean::closure_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_nodeInfo(x_15);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_20, 0, x_9);
lean::closure_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_app___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("app");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
x_4 = l_Lean_Parser_Term_app;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_parser_parser(obj*);
obj* initialize_init_lean_parser_level(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_term(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_level(w);
if (io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTermParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTermParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTermParsingTable"), l_Lean_Parser_builtinTermParsingTable);
l_Lean_Parser_regBuiltinTermParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__1);
l_Lean_Parser_regBuiltinTermParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinTermParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_termParser___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_termParser___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_termParser___elambda__1___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "termParser"), 2, l_Lean_Parser_termParser___boxed);
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__1);
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_ident___spec__3___closed__2);
l_Lean_Parser_Term_ident = _init_l_Lean_Parser_Term_ident();
lean::mark_persistent(l_Lean_Parser_Term_ident);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "ident"), l_Lean_Parser_Term_ident);
l___regBuiltinParser_Lean_Parser_Term_ident___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_ident___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_ident___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_ident(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_num = _init_l_Lean_Parser_Term_num();
lean::mark_persistent(l_Lean_Parser_Term_num);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "num"), l_Lean_Parser_Term_num);
l___regBuiltinParser_Lean_Parser_Term_num___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_num___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_num___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_num(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_str = _init_l_Lean_Parser_Term_str();
lean::mark_persistent(l_Lean_Parser_Term_str);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "str"), l_Lean_Parser_Term_str);
l___regBuiltinParser_Lean_Parser_Term_str___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_str___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_str___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_str(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_type = _init_l_Lean_Parser_Term_type();
lean::mark_persistent(l_Lean_Parser_Term_type);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "type"), l_Lean_Parser_Term_type);
l___regBuiltinParser_Lean_Parser_Term_type___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_type___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_type___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_type(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sort = _init_l_Lean_Parser_Term_sort();
lean::mark_persistent(l_Lean_Parser_Term_sort);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sort"), l_Lean_Parser_Term_sort);
l___regBuiltinParser_Lean_Parser_Term_sort___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_sort___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_sort___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_sort(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_hole = _init_l_Lean_Parser_Term_hole();
lean::mark_persistent(l_Lean_Parser_Term_hole);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "hole"), l_Lean_Parser_Term_hole);
l___regBuiltinParser_Lean_Parser_Term_hole___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_hole___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_hole___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_hole(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_cdot = _init_l_Lean_Parser_Term_cdot();
lean::mark_persistent(l_Lean_Parser_Term_cdot);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "cdot"), l_Lean_Parser_Term_cdot);
l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_cdot(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_parenSpecial = _init_l_Lean_Parser_Term_parenSpecial();
lean::mark_persistent(l_Lean_Parser_Term_parenSpecial);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "parenSpecial"), l_Lean_Parser_Term_parenSpecial);
l_Lean_Parser_Term_paren = _init_l_Lean_Parser_Term_paren();
lean::mark_persistent(l_Lean_Parser_Term_paren);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "paren"), l_Lean_Parser_Term_paren);
l___regBuiltinParser_Lean_Parser_Term_paren___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_paren___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_paren___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_paren(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_app = _init_l_Lean_Parser_Term_app();
lean::mark_persistent(l_Lean_Parser_Term_app);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "app"), l_Lean_Parser_Term_app);
l___regBuiltinParser_Lean_Parser_Term_app___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_app___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_app___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_app(w);
if (io_result_is_error(w)) return w;
return w;
}
