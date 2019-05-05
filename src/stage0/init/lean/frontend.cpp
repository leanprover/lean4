// Lean compiler output
// Module: init.lean.frontend
// Imports: init.default init.lean.parser.module init.lean.expander init.lean.elaborator init.lean.util init.io
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
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
obj* l_Lean_KVMap_setBool(obj*, obj*, uint8);
extern obj* l_Lean_Parser_Term_builtinTrailingParsers_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Term_builtinLeadingParsers;
obj* l_Lean_Elaborator_processCommand(obj*, obj*, obj*);
obj* l_Lean_mkConfig(obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__7;
obj* l_Lean_processFile___lambda__1___closed__1;
obj* l_Lean_runFrontend___closed__1;
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_builtinCommandParsers;
obj* l_List_reverse___rarg(obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__4;
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3(obj*, obj*, obj*, obj*);
obj* l_ioOfExcept___at_Lean_runFrontend___spec__1(obj*, obj*);
obj* l_Lean_Parser_mkTokenTrie(obj*);
extern obj* l_Lean_Options_empty;
extern obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Nat_repr(obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_processFile___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__4(obj*, obj*, obj*);
extern obj* l_Lean_Expander_builtinTransformers;
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState(obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__2;
extern obj* l_Lean_Parser_Module_eoi;
obj* l_Lean_Parser_tokens___rarg(obj*);
extern obj* l_Lean_Parser_command_builtinCommandParsers_Lean_Parser_HasTokens;
obj* l_List_mfor___main___at_Lean_runFrontend___spec__5(obj*, obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__8;
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
obj* l_Lean_runFrontend(obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__6;
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_Lean_processFile___lambda__1___boxed(obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_runFrontend___spec__3(obj*, obj*, obj*);
obj* l_Lean_processFile___lambda__1(uint8, obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__3;
obj* l_Lean_Message_toString(obj*);
obj* l_Lean_processFile___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1;
obj* l_Lean_profileitPure___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseCommand(obj*, obj*);
obj* lean_process_file(obj*, obj*, uint8, obj*, obj*);
extern obj* l_Lean_Parser_Term_builtinLeadingParsers_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Term_builtinTrailingParsers;
obj* l_Lean_processFile___lambda__1___closed__5;
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_List_mfor___main___at_Lean_runFrontend___spec__2(obj*, obj*, obj*);
obj* l_Lean_FileMap_fromString(obj*);
obj* l_Lean_runFrontend___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_expand(obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHeader(obj*);
obj* l_Lean_processFile___lambda__1___closed__9;
obj* l_Lean_mkConfig(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_tokens___rarg(x_2);
x_4 = l_Lean_Parser_command_builtinCommandParsers_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = l_List_append___rarg(x_3, x_5);
x_7 = l_Lean_Parser_Term_builtinLeadingParsers_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_tokens___rarg(x_7);
x_9 = l_List_append___rarg(x_6, x_8);
x_10 = l_Lean_Parser_Term_builtinTrailingParsers_Lean_Parser_HasTokens;
x_11 = l_Lean_Parser_tokens___rarg(x_10);
x_12 = l_List_append___rarg(x_9, x_11);
x_13 = l_Lean_Parser_mkTokenTrie(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_18 = x_13;
} else {
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
lean::inc(x_1);
x_24 = l_Lean_FileMap_fromString(x_1);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_20);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_Term_builtinLeadingParsers;
x_29 = l_Lean_Parser_Term_builtinTrailingParsers;
x_30 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_29);
lean::cnstr_set(x_30, 3, x_27);
lean::cnstr_set(x_30, 4, x_27);
x_31 = l_Lean_Parser_command_builtinCommandParsers;
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
if (lean::is_scalar(x_22)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_22;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
obj* l_ioOfExcept___at_Lean_runFrontend___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
} else {
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_7;
 lean::cnstr_set_tag(x_7, 1);
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_14 = x_1;
} else {
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseCommand(x_0, x_1);
return x_3;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_expand(x_0, x_1);
return x_3;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_processCommand(x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
lean::dec(x_10);
x_22 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_release(x_12, 1);
 x_24 = x_12;
} else {
 lean::inc(x_22);
 lean::dec(x_12);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_14, 0);
x_27 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_29 = x_14;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_14);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::dec(x_30);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
lean::dec(x_41);
x_46 = l_Lean_FileMap_toPosition(x_38, x_43);
lean::inc(x_22);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_48, 0, x_22);
lean::closure_set(x_48, 1, x_16);
x_49 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1;
x_50 = l_Lean_profileitPure___rarg(x_49, x_46, x_48, x_6);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_51 = lean::cnstr_get(x_50, 0);
x_53 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
x_56 = lean::box(0);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
x_58 = lean::cnstr_get(x_51, 1);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_72; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_22);
lean::dec(x_46);
lean::dec(x_29);
x_65 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_release(x_51, 1);
 x_67 = x_51;
} else {
 lean::inc(x_65);
 lean::dec(x_51);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_58, 0);
lean::inc(x_68);
lean::dec(x_58);
lean::inc(x_0);
x_72 = lean::apply_2(x_0, x_68, x_57);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_79; 
x_73 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_75 = x_72;
} else {
 lean::inc(x_73);
 lean::dec(x_72);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_56);
lean::cnstr_set(x_76, 1, x_73);
lean::inc(x_2);
lean::inc(x_0);
x_79 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_0, x_2, x_76);
if (lean::obj_tag(x_79) == 0)
{
if (x_1 == 0)
{
obj* x_82; obj* x_85; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_27);
lean::dec(x_65);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_19, 8);
lean::inc(x_85);
lean::dec(x_19);
lean::inc(x_4);
x_89 = l_List_reverse___rarg(x_4);
if (lean::is_scalar(x_67)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_67;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_7 = x_91;
x_8 = x_82;
goto lbl_9;
}
else
{
obj* x_92; obj* x_95; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_92 = lean::cnstr_get(x_79, 1);
lean::inc(x_92);
lean::dec(x_79);
x_95 = lean::cnstr_get(x_19, 8);
lean::inc(x_95);
lean::dec(x_19);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_65);
lean::cnstr_set(x_98, 1, x_27);
x_99 = l_List_reverse___rarg(x_98);
if (lean::is_scalar(x_67)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_67;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_95);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
x_7 = x_101;
x_8 = x_92;
goto lbl_9;
}
}
else
{
obj* x_110; obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_2);
lean::dec(x_27);
lean::dec(x_67);
lean::dec(x_65);
x_110 = lean::cnstr_get(x_79, 0);
x_112 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_114 = x_79;
} else {
 lean::inc(x_110);
 lean::inc(x_112);
 lean::dec(x_79);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_110);
lean::cnstr_set(x_115, 1, x_112);
return x_115;
}
}
else
{
obj* x_124; obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_2);
lean::dec(x_27);
lean::dec(x_67);
lean::dec(x_65);
x_124 = lean::cnstr_get(x_72, 0);
x_126 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_128 = x_72;
} else {
 lean::inc(x_124);
 lean::inc(x_126);
 lean::dec(x_72);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_124);
lean::cnstr_set(x_129, 1, x_126);
return x_129;
}
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_141; obj* x_143; 
x_130 = lean::cnstr_get(x_58, 0);
lean::inc(x_130);
lean::dec(x_58);
x_133 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_release(x_51, 1);
 x_135 = x_51;
} else {
 lean::inc(x_133);
 lean::dec(x_51);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_130, 0);
x_138 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_set(x_130, 0, lean::box(0));
 lean::cnstr_set(x_130, 1, lean::box(0));
 x_140 = x_130;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_130);
 x_140 = lean::box(0);
}
x_141 = l_List_reverse___rarg(x_138);
lean::inc(x_0);
x_143 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_0, x_141, x_57);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_146; obj* x_147; obj* x_150; obj* x_151; obj* x_152; 
x_144 = lean::cnstr_get(x_143, 1);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 x_146 = x_143;
} else {
 lean::inc(x_144);
 lean::dec(x_143);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_56);
lean::cnstr_set(x_147, 1, x_144);
lean::inc(x_25);
lean::inc(x_133);
x_150 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_150, 0, x_133);
lean::closure_set(x_150, 1, x_25);
x_151 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_152 = l_Lean_profileitPure___rarg(x_151, x_46, x_150, x_147);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_155; obj* x_157; obj* x_158; 
x_153 = lean::cnstr_get(x_152, 0);
x_155 = lean::cnstr_get(x_152, 1);
if (lean::is_exclusive(x_152)) {
 x_157 = x_152;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::dec(x_152);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_56);
lean::cnstr_set(x_158, 1, x_155);
if (lean::obj_tag(x_153) == 0)
{
lean::dec(x_46);
if (x_1 == 0)
{
obj* x_162; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_172; 
lean::dec(x_27);
lean::dec(x_133);
x_162 = lean::cnstr_get(x_153, 0);
lean::inc(x_162);
lean::dec(x_153);
lean::inc(x_4);
if (lean::is_scalar(x_140)) {
 x_166 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_166 = x_140;
}
lean::cnstr_set(x_166, 0, x_25);
lean::cnstr_set(x_166, 1, x_4);
if (lean::is_scalar(x_135)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_135;
}
lean::cnstr_set(x_167, 0, x_22);
lean::cnstr_set(x_167, 1, x_166);
if (lean::is_scalar(x_29)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_29;
}
lean::cnstr_set(x_168, 0, x_19);
lean::cnstr_set(x_168, 1, x_167);
if (lean::is_scalar(x_24)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_24;
}
lean::cnstr_set(x_169, 0, x_136);
lean::cnstr_set(x_169, 1, x_168);
x_170 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::inc(x_0);
x_172 = lean::apply_2(x_0, x_162, x_158);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; 
x_173 = lean::cnstr_get(x_172, 1);
lean::inc(x_173);
lean::dec(x_172);
x_7 = x_170;
x_8 = x_173;
goto lbl_9;
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_170);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_181 = lean::cnstr_get(x_172, 0);
x_183 = lean::cnstr_get(x_172, 1);
if (lean::is_exclusive(x_172)) {
 x_185 = x_172;
} else {
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_172);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_181);
lean::cnstr_set(x_186, 1, x_183);
return x_186;
}
}
else
{
obj* x_187; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_197; 
x_187 = lean::cnstr_get(x_153, 0);
lean::inc(x_187);
lean::dec(x_153);
x_190 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_190, 0, x_133);
lean::cnstr_set(x_190, 1, x_27);
if (lean::is_scalar(x_140)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_140;
}
lean::cnstr_set(x_191, 0, x_25);
lean::cnstr_set(x_191, 1, x_190);
if (lean::is_scalar(x_135)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_135;
}
lean::cnstr_set(x_192, 0, x_22);
lean::cnstr_set(x_192, 1, x_191);
if (lean::is_scalar(x_29)) {
 x_193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_193 = x_29;
}
lean::cnstr_set(x_193, 0, x_19);
lean::cnstr_set(x_193, 1, x_192);
if (lean::is_scalar(x_24)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_24;
}
lean::cnstr_set(x_194, 0, x_136);
lean::cnstr_set(x_194, 1, x_193);
x_195 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_195, 0, x_194);
lean::inc(x_0);
x_197 = lean::apply_2(x_0, x_187, x_158);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; 
x_198 = lean::cnstr_get(x_197, 1);
lean::inc(x_198);
lean::dec(x_197);
x_7 = x_195;
x_8 = x_198;
goto lbl_9;
}
else
{
obj* x_206; obj* x_208; obj* x_210; obj* x_211; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_195);
x_206 = lean::cnstr_get(x_197, 0);
x_208 = lean::cnstr_get(x_197, 1);
if (lean::is_exclusive(x_197)) {
 x_210 = x_197;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_197);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_206);
lean::cnstr_set(x_211, 1, x_208);
return x_211;
}
}
}
else
{
obj* x_214; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_25);
lean::dec(x_22);
x_214 = lean::cnstr_get(x_153, 0);
lean::inc(x_214);
lean::dec(x_153);
lean::inc(x_214);
lean::inc(x_3);
x_219 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_219, 0, x_3);
lean::closure_set(x_219, 1, x_19);
lean::closure_set(x_219, 2, x_214);
x_220 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_221 = l_Lean_profileitPure___rarg(x_220, x_46, x_219, x_158);
lean::dec(x_46);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_225; obj* x_227; obj* x_228; obj* x_229; obj* x_231; obj* x_233; 
x_223 = lean::cnstr_get(x_221, 0);
x_225 = lean::cnstr_get(x_221, 1);
if (lean::is_exclusive(x_221)) {
 x_227 = x_221;
} else {
 lean::inc(x_223);
 lean::inc(x_225);
 lean::dec(x_221);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_56);
lean::cnstr_set(x_228, 1, x_225);
x_229 = lean::cnstr_get(x_223, 5);
lean::inc(x_229);
x_231 = l_List_reverse___rarg(x_229);
lean::inc(x_0);
x_233 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_0, x_231, x_228);
if (lean::obj_tag(x_233) == 0)
{
obj* x_234; obj* x_237; uint8 x_238; 
x_234 = lean::cnstr_get(x_233, 1);
lean::inc(x_234);
lean::dec(x_233);
x_237 = l_Lean_Parser_Module_eoi;
x_238 = l_Lean_Parser_Syntax_isOfKind___main(x_237, x_214);
lean::dec(x_214);
if (x_238 == 0)
{
if (x_1 == 0)
{
obj* x_242; obj* x_244; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_27);
lean::dec(x_133);
x_242 = lean::cnstr_get(x_223, 6);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_223, 7);
lean::inc(x_244);
lean::inc(x_4);
if (lean::is_scalar(x_140)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_140;
}
lean::cnstr_set(x_247, 0, x_244);
lean::cnstr_set(x_247, 1, x_4);
if (lean::is_scalar(x_135)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_135;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_247);
if (lean::is_scalar(x_29)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_29;
}
lean::cnstr_set(x_249, 0, x_223);
lean::cnstr_set(x_249, 1, x_248);
if (lean::is_scalar(x_24)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_24;
}
lean::cnstr_set(x_250, 0, x_136);
lean::cnstr_set(x_250, 1, x_249);
x_251 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_251, 0, x_250);
x_7 = x_251;
x_8 = x_234;
goto lbl_9;
}
else
{
obj* x_252; obj* x_254; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_252 = lean::cnstr_get(x_223, 6);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_223, 7);
lean::inc(x_254);
x_256 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_256, 0, x_133);
lean::cnstr_set(x_256, 1, x_27);
if (lean::is_scalar(x_140)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_140;
}
lean::cnstr_set(x_257, 0, x_254);
lean::cnstr_set(x_257, 1, x_256);
if (lean::is_scalar(x_135)) {
 x_258 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_258 = x_135;
}
lean::cnstr_set(x_258, 0, x_252);
lean::cnstr_set(x_258, 1, x_257);
if (lean::is_scalar(x_29)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_29;
}
lean::cnstr_set(x_259, 0, x_223);
lean::cnstr_set(x_259, 1, x_258);
if (lean::is_scalar(x_24)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_24;
}
lean::cnstr_set(x_260, 0, x_136);
lean::cnstr_set(x_260, 1, x_259);
x_261 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_261, 0, x_260);
x_7 = x_261;
x_8 = x_234;
goto lbl_9;
}
}
else
{
lean::dec(x_24);
lean::dec(x_29);
lean::dec(x_136);
lean::dec(x_135);
if (x_1 == 0)
{
obj* x_268; obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_27);
lean::dec(x_133);
x_268 = lean::cnstr_get(x_223, 8);
lean::inc(x_268);
lean::dec(x_223);
lean::inc(x_4);
x_272 = l_List_reverse___rarg(x_4);
if (lean::is_scalar(x_140)) {
 x_273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_273 = x_140;
}
lean::cnstr_set(x_273, 0, x_272);
lean::cnstr_set(x_273, 1, x_268);
x_274 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
x_7 = x_274;
x_8 = x_234;
goto lbl_9;
}
else
{
obj* x_275; obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
x_275 = lean::cnstr_get(x_223, 8);
lean::inc(x_275);
lean::dec(x_223);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_133);
lean::cnstr_set(x_278, 1, x_27);
x_279 = l_List_reverse___rarg(x_278);
if (lean::is_scalar(x_140)) {
 x_280 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_280 = x_140;
}
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_280, 1, x_275);
x_281 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_281, 0, x_280);
x_7 = x_281;
x_8 = x_234;
goto lbl_9;
}
}
}
else
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; 
lean::dec(x_214);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_223);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_136);
lean::dec(x_133);
lean::dec(x_140);
lean::dec(x_135);
x_295 = lean::cnstr_get(x_233, 0);
x_297 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 x_299 = x_233;
} else {
 lean::inc(x_295);
 lean::inc(x_297);
 lean::dec(x_233);
 x_299 = lean::box(0);
}
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_295);
lean::cnstr_set(x_300, 1, x_297);
return x_300;
}
}
else
{
obj* x_313; obj* x_315; obj* x_317; obj* x_318; 
lean::dec(x_214);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_136);
lean::dec(x_133);
lean::dec(x_140);
lean::dec(x_135);
x_313 = lean::cnstr_get(x_221, 0);
x_315 = lean::cnstr_get(x_221, 1);
if (lean::is_exclusive(x_221)) {
 x_317 = x_221;
} else {
 lean::inc(x_313);
 lean::inc(x_315);
 lean::dec(x_221);
 x_317 = lean::box(0);
}
if (lean::is_scalar(x_317)) {
 x_318 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_318 = x_317;
}
lean::cnstr_set(x_318, 0, x_313);
lean::cnstr_set(x_318, 1, x_315);
return x_318;
}
}
}
else
{
obj* x_334; obj* x_336; obj* x_338; obj* x_339; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_136);
lean::dec(x_133);
lean::dec(x_140);
lean::dec(x_135);
x_334 = lean::cnstr_get(x_152, 0);
x_336 = lean::cnstr_get(x_152, 1);
if (lean::is_exclusive(x_152)) {
 x_338 = x_152;
} else {
 lean::inc(x_334);
 lean::inc(x_336);
 lean::dec(x_152);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_334);
lean::cnstr_set(x_339, 1, x_336);
return x_339;
}
}
else
{
obj* x_355; obj* x_357; obj* x_359; obj* x_360; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_136);
lean::dec(x_133);
lean::dec(x_140);
lean::dec(x_135);
x_355 = lean::cnstr_get(x_143, 0);
x_357 = lean::cnstr_get(x_143, 1);
if (lean::is_exclusive(x_143)) {
 x_359 = x_143;
} else {
 lean::inc(x_355);
 lean::inc(x_357);
 lean::dec(x_143);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_355);
lean::cnstr_set(x_360, 1, x_357);
return x_360;
}
}
}
else
{
obj* x_372; obj* x_374; obj* x_376; obj* x_377; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_27);
lean::dec(x_29);
x_372 = lean::cnstr_get(x_50, 0);
x_374 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_376 = x_50;
} else {
 lean::inc(x_372);
 lean::inc(x_374);
 lean::dec(x_50);
 x_376 = lean::box(0);
}
if (lean::is_scalar(x_376)) {
 x_377 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_377 = x_376;
}
lean::cnstr_set(x_377, 0, x_372);
lean::cnstr_set(x_377, 1, x_374);
return x_377;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_378; obj* x_381; obj* x_382; 
x_378 = lean::cnstr_get(x_7, 0);
lean::inc(x_378);
lean::dec(x_7);
x_381 = lean::box(0);
x_382 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_8);
x_5 = x_378;
x_6 = x_382;
goto _start;
}
else
{
obj* x_388; obj* x_391; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_388 = lean::cnstr_get(x_7, 0);
lean::inc(x_388);
lean::dec(x_7);
x_391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_391, 0, x_388);
lean::cnstr_set(x_391, 1, x_8);
return x_391;
}
}
}
}
obj* _init_l_Lean_runFrontend___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("as_messages");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_Lean_Options_empty;
x_6 = 1;
x_7 = l_Lean_KVMap_setBool(x_5, x_4, x_6);
return x_7;
}
}
obj* l_Lean_runFrontend(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_Lean_mkConfig(x_0, x_1);
x_9 = l_ioOfExcept___at_Lean_runFrontend___spec__1(x_8, x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_21; 
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = lean::box(0);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
lean::inc(x_10);
x_18 = l_Lean_Parser_parseHeader(x_10);
x_19 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_set(x_18, 1, lean::box(0));
 x_21 = x_18;
} else {
 lean::inc(x_19);
 lean::dec(x_18);
 x_21 = lean::box(0);
}
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
x_25 = lean::cnstr_get(x_19, 0);
lean::inc(x_25);
lean::dec(x_19);
x_28 = lean::box(0);
if (lean::is_scalar(x_21)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_21;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
x_30 = lean::apply_2(x_2, x_25, x_16);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
else
{
obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_29);
x_36 = lean::cnstr_get(x_30, 0);
x_38 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_30);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set(x_41, 1, x_38);
return x_41;
}
}
else
{
obj* x_42; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; 
x_42 = lean::cnstr_get(x_19, 0);
lean::inc(x_42);
lean::dec(x_19);
x_45 = lean::cnstr_get(x_42, 0);
x_47 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 lean::cnstr_set(x_42, 1, lean::box(0));
 x_49 = x_42;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_42);
 x_49 = lean::box(0);
}
x_50 = l_List_reverse___rarg(x_47);
lean::inc(x_50);
lean::inc(x_2);
x_53 = l_List_mfor___main___at_Lean_runFrontend___spec__2(x_2, x_50, x_16);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_54 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_56 = x_53;
} else {
 lean::inc(x_54);
 lean::dec(x_53);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_15);
lean::cnstr_set(x_57, 1, x_54);
x_58 = lean::cnstr_get(x_10, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_58, 0);
lean::inc(x_60);
lean::dec(x_58);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
lean::dec(x_60);
x_66 = l_Lean_Expander_builtinTransformers;
lean::inc(x_63);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::cnstr_get(x_63, 2);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_71 = x_63;
} else {
 lean::inc(x_69);
 lean::dec(x_63);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set(x_72, 2, x_69);
lean::inc(x_10);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_10);
x_75 = l_Lean_runFrontend___closed__1;
lean::inc(x_74);
x_77 = l_Lean_Elaborator_mkState(x_74, x_4, x_75);
x_78 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_49;
}
lean::cnstr_set(x_79, 0, x_68);
lean::cnstr_set(x_79, 1, x_78);
if (lean::is_scalar(x_21)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_21;
}
lean::cnstr_set(x_80, 0, x_10);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_77);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_45);
lean::cnstr_set(x_82, 1, x_81);
x_83 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_2, x_3, x_50, x_74, x_78, x_82, x_57);
return x_83;
}
else
{
obj* x_93; obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_45);
x_93 = lean::cnstr_get(x_53, 0);
x_95 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_97 = x_53;
} else {
 lean::inc(x_93);
 lean::inc(x_95);
 lean::dec(x_53);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_93);
lean::cnstr_set(x_98, 1, x_95);
return x_98;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_103 = lean::cnstr_get(x_9, 0);
x_105 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_107 = x_9;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_9);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_103);
lean::cnstr_set(x_108, 1, x_105);
return x_108;
}
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
x_8 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_0, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_Lean_runFrontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_Lean_runFrontend(x_0, x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"pos_col\": ");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"severity\": ");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("information");
x_1 = l_String_quote(x_0);
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"caption\": ");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"text\": ");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("warning");
x_1 = l_String_quote(x_0);
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("error");
x_1 = l_String_quote(x_0);
return x_1;
}
}
obj* l_Lean_processFile___lambda__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Message_toString(x_1);
x_4 = l_IO_println___at_HasRepr_HasEval___spec__1(x_3, x_2);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_31; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_10 = l_Nat_repr(x_8);
x_11 = l_Lean_processFile___lambda__1___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_Lean_processFile___lambda__1___closed__2;
x_15 = lean::string_append(x_12, x_14);
x_16 = lean::cnstr_get(x_6, 1);
lean::inc(x_16);
lean::dec(x_6);
x_19 = l_Nat_repr(x_16);
x_20 = lean::string_append(x_15, x_19);
lean::dec(x_19);
x_22 = l_Lean_processFile___lambda__1___closed__3;
x_23 = lean::string_append(x_20, x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_25 = lean::cnstr_get(x_1, 3);
lean::inc(x_25);
x_27 = l_String_quote(x_25);
x_28 = lean::cnstr_get(x_1, 4);
lean::inc(x_28);
lean::dec(x_1);
x_31 = l_String_quote(x_28);
switch (x_24) {
case 0:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
x_32 = l_Lean_processFile___lambda__1___closed__4;
x_33 = lean::string_append(x_23, x_32);
x_34 = l_Lean_processFile___lambda__1___closed__5;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::string_append(x_35, x_27);
lean::dec(x_27);
x_38 = l_Lean_processFile___lambda__1___closed__6;
x_39 = lean::string_append(x_36, x_38);
x_40 = lean::string_append(x_39, x_31);
lean::dec(x_31);
x_42 = l_Lean_processFile___lambda__1___closed__7;
x_43 = lean::string_append(x_40, x_42);
x_44 = l_IO_println___at_HasRepr_HasEval___spec__1(x_43, x_2);
lean::dec(x_43);
return x_44;
}
case 1:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
x_46 = l_Lean_processFile___lambda__1___closed__8;
x_47 = lean::string_append(x_23, x_46);
x_48 = l_Lean_processFile___lambda__1___closed__5;
x_49 = lean::string_append(x_47, x_48);
x_50 = lean::string_append(x_49, x_27);
lean::dec(x_27);
x_52 = l_Lean_processFile___lambda__1___closed__6;
x_53 = lean::string_append(x_50, x_52);
x_54 = lean::string_append(x_53, x_31);
lean::dec(x_31);
x_56 = l_Lean_processFile___lambda__1___closed__7;
x_57 = lean::string_append(x_54, x_56);
x_58 = l_IO_println___at_HasRepr_HasEval___spec__1(x_57, x_2);
lean::dec(x_57);
return x_58;
}
default:
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
x_60 = l_Lean_processFile___lambda__1___closed__9;
x_61 = lean::string_append(x_23, x_60);
x_62 = l_Lean_processFile___lambda__1___closed__5;
x_63 = lean::string_append(x_61, x_62);
x_64 = lean::string_append(x_63, x_27);
lean::dec(x_27);
x_66 = l_Lean_processFile___lambda__1___closed__6;
x_67 = lean::string_append(x_64, x_66);
x_68 = lean::string_append(x_67, x_31);
lean::dec(x_31);
x_70 = l_Lean_processFile___lambda__1___closed__7;
x_71 = lean::string_append(x_68, x_70);
x_72 = l_IO_println___at_HasRepr_HasEval___spec__1(x_71, x_2);
lean::dec(x_71);
return x_72;
}
}
}
}
}
obj* _init_l_Lean_processFile___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = l_Nat_repr(x_0);
x_2 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::mk_string(", \"pos_col\": ");
x_6 = lean::string_append(x_3, x_5);
lean::dec(x_5);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_Nat_repr(x_8);
x_10 = lean::string_append(x_6, x_9);
lean::dec(x_9);
x_12 = lean::mk_string(", \"severity\": ");
x_13 = lean::string_append(x_10, x_12);
lean::dec(x_12);
x_15 = lean::mk_string("error");
x_16 = l_String_quote(x_15);
x_17 = lean::string_append(x_13, x_16);
lean::dec(x_16);
x_19 = lean::mk_string(", \"caption\": ");
x_20 = lean::string_append(x_17, x_19);
lean::dec(x_19);
x_22 = lean::mk_string("");
x_23 = l_String_quote(x_22);
x_24 = lean::string_append(x_20, x_23);
lean::dec(x_23);
x_26 = lean::mk_string(", \"text\": ");
x_27 = lean::string_append(x_24, x_26);
lean::dec(x_26);
return x_27;
}
}
obj* lean_process_file(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_9; 
x_5 = lean::box(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_processFile___lambda__1___boxed), 3, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = 0;
lean::inc(x_0);
x_9 = l_Lean_runFrontend(x_0, x_1, x_6, x_7, x_3, x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_11 = lean::cnstr_get(x_9, 0);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_26 = x_9;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
x_27 = lean::box(0);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
if (x_2 == 0)
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::box(0);
x_30 = l_Lean_Elaborator_notation_elaborate___closed__1;
x_31 = 2;
x_32 = l_String_splitAux___main___closed__1;
lean::inc(x_22);
x_34 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_34, 0, x_0);
lean::cnstr_set(x_34, 1, x_30);
lean::cnstr_set(x_34, 2, x_29);
lean::cnstr_set(x_34, 3, x_32);
lean::cnstr_set(x_34, 4, x_22);
lean::cnstr_set_scalar(x_34, sizeof(void*)*5, x_31);
x_35 = x_34;
x_36 = l_Lean_Message_toString(x_35);
x_37 = l_IO_println___at_HasRepr_HasEval___spec__1(x_36, x_28);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
 lean::cnstr_set_tag(x_41, 1);
}
lean::cnstr_set(x_42, 0, x_22);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_22);
x_44 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_0);
lean::inc(x_22);
x_52 = l_String_quote(x_22);
x_53 = l_Lean_processFile___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_Lean_processFile___lambda__1___closed__7;
x_57 = lean::string_append(x_54, x_56);
x_58 = l_IO_println___at_HasRepr_HasEval___spec__1(x_57, x_28);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_62 = x_58;
} else {
 lean::inc(x_60);
 lean::dec(x_58);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
 lean::cnstr_set_tag(x_62, 1);
}
lean::cnstr_set(x_63, 0, x_22);
lean::cnstr_set(x_63, 1, x_60);
return x_63;
}
else
{
obj* x_65; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_22);
x_65 = lean::cnstr_get(x_58, 0);
x_67 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 x_69 = x_58;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_58);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_65);
lean::cnstr_set(x_70, 1, x_67);
return x_70;
}
}
}
}
}
obj* l_Lean_processFile___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_processFile___lambda__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_processFile___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean_process_file(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_parser_module(obj*);
obj* initialize_init_lean_expander(obj*);
obj* initialize_init_lean_elaborator(obj*);
obj* initialize_init_lean_util(obj*);
obj* initialize_init_io(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_frontend(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expander(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_util(w);
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
if (io_result_is_error(w)) return w;
 l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1 = _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1();
lean::mark_persistent(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1);
 l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2 = _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2();
lean::mark_persistent(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2);
 l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3 = _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3();
lean::mark_persistent(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3);
 l_Lean_runFrontend___closed__1 = _init_l_Lean_runFrontend___closed__1();
lean::mark_persistent(l_Lean_runFrontend___closed__1);
 l_Lean_processFile___lambda__1___closed__1 = _init_l_Lean_processFile___lambda__1___closed__1();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__1);
 l_Lean_processFile___lambda__1___closed__2 = _init_l_Lean_processFile___lambda__1___closed__2();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__2);
 l_Lean_processFile___lambda__1___closed__3 = _init_l_Lean_processFile___lambda__1___closed__3();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__3);
 l_Lean_processFile___lambda__1___closed__4 = _init_l_Lean_processFile___lambda__1___closed__4();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__4);
 l_Lean_processFile___lambda__1___closed__5 = _init_l_Lean_processFile___lambda__1___closed__5();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__5);
 l_Lean_processFile___lambda__1___closed__6 = _init_l_Lean_processFile___lambda__1___closed__6();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__6);
 l_Lean_processFile___lambda__1___closed__7 = _init_l_Lean_processFile___lambda__1___closed__7();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__7);
 l_Lean_processFile___lambda__1___closed__8 = _init_l_Lean_processFile___lambda__1___closed__8();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__8);
 l_Lean_processFile___lambda__1___closed__9 = _init_l_Lean_processFile___lambda__1___closed__9();
lean::mark_persistent(l_Lean_processFile___lambda__1___closed__9);
 l_Lean_processFile___closed__1 = _init_l_Lean_processFile___closed__1();
lean::mark_persistent(l_Lean_processFile___closed__1);
return w;
}
