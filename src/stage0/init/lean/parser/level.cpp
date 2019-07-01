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
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
obj* l_Lean_Parser_Level_paren;
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Level_max;
obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit;
obj* l___regBuiltinParser_Lean_Parser_Level_num___closed__1;
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_levelParser(uint8, obj*);
obj* l_Lean_Parser_Level_num;
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj*);
obj* l_Lean_Parser_levelParser___elambda__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_hole(obj*);
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_many1Fn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1;
obj* l_Lean_Parser_levelParser___boxed(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_imax(obj*);
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_imax;
extern obj* l_Lean_Parser_maxPrec;
obj* l___regBuiltinParser_Lean_Parser_Level_hole___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj*);
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_levelParser___elambda__1(uint8);
obj* l___regBuiltinParser_Lean_Parser_Level_max(obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_levelParser___elambda__1___boxed(obj*);
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_ident___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
obj* l_Lean_Parser_levelParser___elambda__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_num(obj*);
obj* l_Lean_Parser_Level_hole;
obj* l___regBuiltinParser_Lean_Parser_Level_paren(obj*);
obj* l_Lean_Parser_Level_ident;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l___regBuiltinParser_Lean_Parser_Level_max___closed__1;
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Level_imax___closed__1;
obj* l_Lean_Parser_levelParser___elambda__1___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Level_paren___closed__1;
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
obj* _init_l_Lean_Parser_levelParser___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("universe level");
return x_1;
}
}
obj* l_Lean_Parser_levelParser___elambda__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_levelParser___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_builtinLevelParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_levelParser___elambda__1(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_levelParser(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_levelParser___elambda__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_levelParser___elambda__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_levelParser___elambda__1___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_levelParser___elambda__1(x_2);
return x_3;
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
obj* _init_l_Lean_Parser_Level_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("(");
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = 0;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_levelParser(x_15, x_16);
x_18 = lean::box(0);
x_19 = lean::mk_string(")");
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolInfo(x_19, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_21, 0, x_19);
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_andthenInfo(x_22, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_16);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_21);
x_26 = l_Lean_Parser_andthenInfo(x_13, x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_14);
lean::closure_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_nodeInfo(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_29, 0, x_9);
lean::closure_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Level_paren___closed__1() {
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
obj* l___regBuiltinParser_Lean_Parser_Level_paren(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_paren___closed__1;
x_4 = l_Lean_Parser_Level_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_max() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("max");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
lean::inc(x_8);
x_11 = l_Lean_Parser_symbolInfo(x_8, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_12, 0, x_8);
x_13 = 0;
x_14 = l_Lean_Parser_maxPrec;
x_15 = l_Lean_Parser_levelParser(x_13, x_14);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::box(x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_17);
x_20 = l_Lean_Parser_andthenInfo(x_11, x_16);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_12);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Level_max___closed__1() {
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
obj* l___regBuiltinParser_Lean_Parser_Level_max(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_max___closed__1;
x_4 = l_Lean_Parser_Level_max;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_imax() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("imax");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
lean::inc(x_8);
x_11 = l_Lean_Parser_symbolInfo(x_8, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_12, 0, x_8);
x_13 = 0;
x_14 = l_Lean_Parser_maxPrec;
x_15 = l_Lean_Parser_levelParser(x_13, x_14);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::box(x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_17);
x_20 = l_Lean_Parser_andthenInfo(x_11, x_16);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_12);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Level_imax___closed__1() {
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
obj* l___regBuiltinParser_Lean_Parser_Level_imax(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_imax___closed__1;
x_4 = l_Lean_Parser_Level_imax;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_hole() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("_");
lean::inc(x_11);
x_12 = l_Lean_Parser_symbolInfo(x_11, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = l_Lean_Parser_nodeInfo(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Level_hole___closed__1() {
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
obj* l___regBuiltinParser_Lean_Parser_Level_hole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_hole___closed__1;
x_4 = l_Lean_Parser_Level_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_num() {
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
obj* _init_l_Lean_Parser_Level_ident() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
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
obj* _init_l_Lean_Parser_Level_addLit() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("addLit");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_nat_obj(65u);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("+");
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::mk_string("numLit");
x_16 = l_Lean_Parser_mkAtomicInfo(x_15);
x_17 = 1;
x_18 = lean::box(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numLitFn___boxed), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_epsilonInfo;
x_23 = l_Lean_Parser_andthenInfo(x_22, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_21);
x_26 = l_Lean_Parser_nodeInfo(x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_9);
lean::closure_set(x_27, 1, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1() {
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
obj* l___regBuiltinParser_Lean_Parser_Level_addLit(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinLevelParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1;
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
l_Lean_Parser_levelParser___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_levelParser___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_levelParser___elambda__1___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "levelParser"), 2, l_Lean_Parser_levelParser___boxed);
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean::mark_persistent(l_Lean_Parser_Level_paren);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "paren"), l_Lean_Parser_Level_paren);
l___regBuiltinParser_Lean_Parser_Level_paren___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_paren___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_paren___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_paren(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
lean::mark_persistent(l_Lean_Parser_Level_max);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "max"), l_Lean_Parser_Level_max);
l___regBuiltinParser_Lean_Parser_Level_max___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_max___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_max___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_max(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
lean::mark_persistent(l_Lean_Parser_Level_imax);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "imax"), l_Lean_Parser_Level_imax);
l___regBuiltinParser_Lean_Parser_Level_imax___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_imax___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_imax___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_imax(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
lean::mark_persistent(l_Lean_Parser_Level_hole);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "hole"), l_Lean_Parser_Level_hole);
l___regBuiltinParser_Lean_Parser_Level_hole___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_hole___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_hole___closed__1);
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
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean::mark_persistent(l_Lean_Parser_Level_addLit);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Level"), "addLit"), l_Lean_Parser_Level_addLit);
l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Level_addLit___closed__1);
w = l___regBuiltinParser_Lean_Parser_Level_addLit(w);
if (io_result_is_error(w)) return w;
return w;
}
