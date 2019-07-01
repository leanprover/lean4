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
obj* l_Lean_Parser_strLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_num;
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1(uint8);
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Term_hole;
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ident(obj*);
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_levelParser(uint8, obj*);
obj* l_Lean_Parser_Term_str;
obj* l_Lean_Parser_levelParser___elambda__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_many1Fn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ident___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
obj* l_Lean_Parser_termParser___boxed(obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___rarg___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Term_sort;
obj* l_Lean_Parser_Term_ident;
obj* l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
extern obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_termParser___elambda__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj*);
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj*);
obj* l_Lean_Parser_Term_type;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
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
obj* _init_l_Lean_Parser_Term_ident() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
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
lean::inc(x_15);
x_16 = l_Lean_Parser_symbolInfo(x_15, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_17, 0, x_15);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Lean_Parser_levelParser(x_11, x_18);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
lean::dec(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___rarg___boxed), 4, 1);
lean::closure_set(x_21, 0, x_18);
x_22 = lean::box(x_11);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::mk_string("}");
lean::inc(x_24);
x_25 = l_Lean_Parser_symbolInfo(x_24, x_14);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_26, 0, x_24);
x_27 = l_Lean_Parser_andthenInfo(x_20, x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_28, 0, x_23);
lean::closure_set(x_28, 1, x_26);
x_29 = l_Lean_Parser_andthenInfo(x_16, x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_30, 0, x_17);
lean::closure_set(x_30, 1, x_28);
x_31 = l_Lean_Parser_noFirstTokenInfo(x_29);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_10, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_13);
lean::closure_set(x_34, 1, x_32);
x_35 = l_Lean_Parser_nodeInfo(x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_9);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_nodeInfo(x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_nodeInfo(x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_nodeInfo(x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
l_Lean_Parser_Term_app = _init_l_Lean_Parser_Term_app();
lean::mark_persistent(l_Lean_Parser_Term_app);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "app"), l_Lean_Parser_Term_app);
l___regBuiltinParser_Lean_Parser_Term_app___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_app___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_app___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_app(w);
if (io_result_is_error(w)) return w;
return w;
}
