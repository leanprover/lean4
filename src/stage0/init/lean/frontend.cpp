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
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__4(obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
extern obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Nat_repr(obj*);
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed(obj*, obj*, obj*);
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__5(obj*, obj*, obj*);
obj* l_Lean_processFile___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
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
obj* l_Lean_processFile___lambda__1___closed__8;
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
obj* l_Lean_runFrontend(obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__2(obj*, obj*, obj*);
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__3(obj*, obj*, obj*);
obj* l_Lean_processFile___lambda__1___closed__6;
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_Lean_processFile___lambda__1___boxed(obj*, obj*, obj*);
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
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__3(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_List_mmap_x_27___main___at_Lean_runFrontend___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
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
x_56 = lean::cnstr_get(x_51, 0);
x_58 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_set(x_51, 1, lean::box(0));
 x_60 = x_51;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_51);
 x_60 = lean::box(0);
}
x_61 = lean::box(0);
if (lean::is_scalar(x_55)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_55;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_53);
if (lean::obj_tag(x_58) == 0)
{
obj* x_68; obj* x_72; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_22);
lean::dec(x_46);
lean::dec(x_29);
x_68 = lean::cnstr_get(x_58, 0);
lean::inc(x_68);
lean::dec(x_58);
lean::inc(x_0);
x_72 = lean::apply_2(x_0, x_68, x_62);
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
lean::cnstr_set(x_76, 0, x_61);
lean::cnstr_set(x_76, 1, x_73);
lean::inc(x_2);
lean::inc(x_0);
x_79 = l_List_mmap_x_27___main___at_Lean_runFrontend___spec__3(x_0, x_2, x_76);
if (lean::obj_tag(x_79) == 0)
{
if (x_1 == 0)
{
obj* x_82; obj* x_85; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_27);
lean::dec(x_56);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_19, 8);
lean::inc(x_85);
lean::dec(x_19);
lean::inc(x_4);
x_89 = l_List_reverse___rarg(x_4);
if (lean::is_scalar(x_60)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_60;
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
lean::cnstr_set(x_98, 0, x_56);
lean::cnstr_set(x_98, 1, x_27);
x_99 = l_List_reverse___rarg(x_98);
if (lean::is_scalar(x_60)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_60;
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
lean::dec(x_56);
lean::dec(x_60);
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
lean::dec(x_56);
lean::dec(x_60);
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
obj* x_130; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_140; 
x_130 = lean::cnstr_get(x_58, 0);
lean::inc(x_130);
lean::dec(x_58);
x_133 = lean::cnstr_get(x_130, 0);
x_135 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_set(x_130, 0, lean::box(0));
 lean::cnstr_set(x_130, 1, lean::box(0));
 x_137 = x_130;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_130);
 x_137 = lean::box(0);
}
x_138 = l_List_reverse___rarg(x_135);
lean::inc(x_0);
x_140 = l_List_mmap_x_27___main___at_Lean_runFrontend___spec__4(x_0, x_138, x_62);
if (lean::obj_tag(x_140) == 0)
{
obj* x_141; obj* x_143; obj* x_144; obj* x_147; obj* x_148; obj* x_149; 
x_141 = lean::cnstr_get(x_140, 1);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 x_143 = x_140;
} else {
 lean::inc(x_141);
 lean::dec(x_140);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_61);
lean::cnstr_set(x_144, 1, x_141);
lean::inc(x_25);
lean::inc(x_56);
x_147 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_147, 0, x_56);
lean::closure_set(x_147, 1, x_25);
x_148 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_149 = l_Lean_profileitPure___rarg(x_148, x_46, x_147, x_144);
if (lean::obj_tag(x_149) == 0)
{
obj* x_150; obj* x_152; obj* x_154; obj* x_155; 
x_150 = lean::cnstr_get(x_149, 0);
x_152 = lean::cnstr_get(x_149, 1);
if (lean::is_exclusive(x_149)) {
 x_154 = x_149;
} else {
 lean::inc(x_150);
 lean::inc(x_152);
 lean::dec(x_149);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_61);
lean::cnstr_set(x_155, 1, x_152);
if (lean::obj_tag(x_150) == 0)
{
lean::dec(x_46);
if (x_1 == 0)
{
obj* x_159; obj* x_163; 
lean::dec(x_27);
lean::dec(x_56);
x_159 = lean::cnstr_get(x_150, 0);
lean::inc(x_159);
lean::dec(x_150);
lean::inc(x_0);
x_163 = lean::apply_2(x_0, x_159, x_155);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_164 = lean::cnstr_get(x_163, 1);
lean::inc(x_164);
lean::dec(x_163);
lean::inc(x_4);
if (lean::is_scalar(x_137)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_137;
}
lean::cnstr_set(x_168, 0, x_25);
lean::cnstr_set(x_168, 1, x_4);
if (lean::is_scalar(x_60)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_60;
}
lean::cnstr_set(x_169, 0, x_22);
lean::cnstr_set(x_169, 1, x_168);
if (lean::is_scalar(x_29)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_29;
}
lean::cnstr_set(x_170, 0, x_19);
lean::cnstr_set(x_170, 1, x_169);
if (lean::is_scalar(x_24)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_24;
}
lean::cnstr_set(x_171, 0, x_133);
lean::cnstr_set(x_171, 1, x_170);
x_172 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_172, 0, x_171);
x_7 = x_172;
x_8 = x_164;
goto lbl_9;
}
else
{
obj* x_185; obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_185 = lean::cnstr_get(x_163, 0);
x_187 = lean::cnstr_get(x_163, 1);
if (lean::is_exclusive(x_163)) {
 x_189 = x_163;
} else {
 lean::inc(x_185);
 lean::inc(x_187);
 lean::dec(x_163);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_185);
lean::cnstr_set(x_190, 1, x_187);
return x_190;
}
}
else
{
obj* x_191; obj* x_195; 
x_191 = lean::cnstr_get(x_150, 0);
lean::inc(x_191);
lean::dec(x_150);
lean::inc(x_0);
x_195 = lean::apply_2(x_0, x_191, x_155);
if (lean::obj_tag(x_195) == 0)
{
obj* x_196; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_196 = lean::cnstr_get(x_195, 1);
lean::inc(x_196);
lean::dec(x_195);
x_199 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_199, 0, x_56);
lean::cnstr_set(x_199, 1, x_27);
if (lean::is_scalar(x_137)) {
 x_200 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_200 = x_137;
}
lean::cnstr_set(x_200, 0, x_25);
lean::cnstr_set(x_200, 1, x_199);
if (lean::is_scalar(x_60)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_60;
}
lean::cnstr_set(x_201, 0, x_22);
lean::cnstr_set(x_201, 1, x_200);
if (lean::is_scalar(x_29)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_29;
}
lean::cnstr_set(x_202, 0, x_19);
lean::cnstr_set(x_202, 1, x_201);
if (lean::is_scalar(x_24)) {
 x_203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_203 = x_24;
}
lean::cnstr_set(x_203, 0, x_133);
lean::cnstr_set(x_203, 1, x_202);
x_204 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_204, 0, x_203);
x_7 = x_204;
x_8 = x_196;
goto lbl_9;
}
else
{
obj* x_219; obj* x_221; obj* x_223; obj* x_224; 
lean::dec(x_24);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_2);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_219 = lean::cnstr_get(x_195, 0);
x_221 = lean::cnstr_get(x_195, 1);
if (lean::is_exclusive(x_195)) {
 x_223 = x_195;
} else {
 lean::inc(x_219);
 lean::inc(x_221);
 lean::dec(x_195);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_219);
lean::cnstr_set(x_224, 1, x_221);
return x_224;
}
}
}
else
{
obj* x_227; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_25);
lean::dec(x_22);
x_227 = lean::cnstr_get(x_150, 0);
lean::inc(x_227);
lean::dec(x_150);
lean::inc(x_227);
lean::inc(x_3);
x_232 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_232, 0, x_3);
lean::closure_set(x_232, 1, x_19);
lean::closure_set(x_232, 2, x_227);
x_233 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_234 = l_Lean_profileitPure___rarg(x_233, x_46, x_232, x_155);
lean::dec(x_46);
if (lean::obj_tag(x_234) == 0)
{
obj* x_236; obj* x_238; obj* x_240; obj* x_241; obj* x_242; obj* x_244; obj* x_246; 
x_236 = lean::cnstr_get(x_234, 0);
x_238 = lean::cnstr_get(x_234, 1);
if (lean::is_exclusive(x_234)) {
 x_240 = x_234;
} else {
 lean::inc(x_236);
 lean::inc(x_238);
 lean::dec(x_234);
 x_240 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_61);
lean::cnstr_set(x_241, 1, x_238);
x_242 = lean::cnstr_get(x_236, 5);
lean::inc(x_242);
x_244 = l_List_reverse___rarg(x_242);
lean::inc(x_0);
x_246 = l_List_mmap_x_27___main___at_Lean_runFrontend___spec__5(x_0, x_244, x_241);
if (lean::obj_tag(x_246) == 0)
{
obj* x_247; obj* x_250; uint8 x_251; 
x_247 = lean::cnstr_get(x_246, 1);
lean::inc(x_247);
lean::dec(x_246);
x_250 = l_Lean_Parser_Module_eoi;
x_251 = l_Lean_Parser_Syntax_isOfKind___main(x_250, x_227);
lean::dec(x_227);
if (x_251 == 0)
{
if (x_1 == 0)
{
obj* x_255; obj* x_257; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_27);
lean::dec(x_56);
x_255 = lean::cnstr_get(x_236, 6);
lean::inc(x_255);
x_257 = lean::cnstr_get(x_236, 7);
lean::inc(x_257);
lean::inc(x_4);
if (lean::is_scalar(x_137)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_137;
}
lean::cnstr_set(x_260, 0, x_257);
lean::cnstr_set(x_260, 1, x_4);
if (lean::is_scalar(x_60)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_60;
}
lean::cnstr_set(x_261, 0, x_255);
lean::cnstr_set(x_261, 1, x_260);
if (lean::is_scalar(x_29)) {
 x_262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_262 = x_29;
}
lean::cnstr_set(x_262, 0, x_236);
lean::cnstr_set(x_262, 1, x_261);
if (lean::is_scalar(x_24)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_24;
}
lean::cnstr_set(x_263, 0, x_133);
lean::cnstr_set(x_263, 1, x_262);
x_264 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_264, 0, x_263);
x_7 = x_264;
x_8 = x_247;
goto lbl_9;
}
else
{
obj* x_265; obj* x_267; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_265 = lean::cnstr_get(x_236, 6);
lean::inc(x_265);
x_267 = lean::cnstr_get(x_236, 7);
lean::inc(x_267);
x_269 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_269, 0, x_56);
lean::cnstr_set(x_269, 1, x_27);
if (lean::is_scalar(x_137)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_137;
}
lean::cnstr_set(x_270, 0, x_267);
lean::cnstr_set(x_270, 1, x_269);
if (lean::is_scalar(x_60)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_60;
}
lean::cnstr_set(x_271, 0, x_265);
lean::cnstr_set(x_271, 1, x_270);
if (lean::is_scalar(x_29)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_29;
}
lean::cnstr_set(x_272, 0, x_236);
lean::cnstr_set(x_272, 1, x_271);
if (lean::is_scalar(x_24)) {
 x_273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_273 = x_24;
}
lean::cnstr_set(x_273, 0, x_133);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
x_7 = x_274;
x_8 = x_247;
goto lbl_9;
}
}
else
{
lean::dec(x_24);
lean::dec(x_29);
lean::dec(x_60);
lean::dec(x_133);
if (x_1 == 0)
{
obj* x_281; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_27);
lean::dec(x_56);
x_281 = lean::cnstr_get(x_236, 8);
lean::inc(x_281);
lean::dec(x_236);
lean::inc(x_4);
x_285 = l_List_reverse___rarg(x_4);
if (lean::is_scalar(x_137)) {
 x_286 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_286 = x_137;
}
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_281);
x_287 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_287, 0, x_286);
x_7 = x_287;
x_8 = x_247;
goto lbl_9;
}
else
{
obj* x_288; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
x_288 = lean::cnstr_get(x_236, 8);
lean::inc(x_288);
lean::dec(x_236);
x_291 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_291, 0, x_56);
lean::cnstr_set(x_291, 1, x_27);
x_292 = l_List_reverse___rarg(x_291);
if (lean::is_scalar(x_137)) {
 x_293 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_293 = x_137;
}
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_288);
x_294 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_294, 0, x_293);
x_7 = x_294;
x_8 = x_247;
goto lbl_9;
}
}
}
else
{
obj* x_308; obj* x_310; obj* x_312; obj* x_313; 
lean::dec(x_227);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_236);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_308 = lean::cnstr_get(x_246, 0);
x_310 = lean::cnstr_get(x_246, 1);
if (lean::is_exclusive(x_246)) {
 x_312 = x_246;
} else {
 lean::inc(x_308);
 lean::inc(x_310);
 lean::dec(x_246);
 x_312 = lean::box(0);
}
if (lean::is_scalar(x_312)) {
 x_313 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_313 = x_312;
}
lean::cnstr_set(x_313, 0, x_308);
lean::cnstr_set(x_313, 1, x_310);
return x_313;
}
}
else
{
obj* x_326; obj* x_328; obj* x_330; obj* x_331; 
lean::dec(x_227);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_326 = lean::cnstr_get(x_234, 0);
x_328 = lean::cnstr_get(x_234, 1);
if (lean::is_exclusive(x_234)) {
 x_330 = x_234;
} else {
 lean::inc(x_326);
 lean::inc(x_328);
 lean::dec(x_234);
 x_330 = lean::box(0);
}
if (lean::is_scalar(x_330)) {
 x_331 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_331 = x_330;
}
lean::cnstr_set(x_331, 0, x_326);
lean::cnstr_set(x_331, 1, x_328);
return x_331;
}
}
}
else
{
obj* x_347; obj* x_349; obj* x_351; obj* x_352; 
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
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_347 = lean::cnstr_get(x_149, 0);
x_349 = lean::cnstr_get(x_149, 1);
if (lean::is_exclusive(x_149)) {
 x_351 = x_149;
} else {
 lean::inc(x_347);
 lean::inc(x_349);
 lean::dec(x_149);
 x_351 = lean::box(0);
}
if (lean::is_scalar(x_351)) {
 x_352 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_352 = x_351;
}
lean::cnstr_set(x_352, 0, x_347);
lean::cnstr_set(x_352, 1, x_349);
return x_352;
}
}
else
{
obj* x_368; obj* x_370; obj* x_372; obj* x_373; 
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
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_133);
lean::dec(x_137);
x_368 = lean::cnstr_get(x_140, 0);
x_370 = lean::cnstr_get(x_140, 1);
if (lean::is_exclusive(x_140)) {
 x_372 = x_140;
} else {
 lean::inc(x_368);
 lean::inc(x_370);
 lean::dec(x_140);
 x_372 = lean::box(0);
}
if (lean::is_scalar(x_372)) {
 x_373 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_373 = x_372;
}
lean::cnstr_set(x_373, 0, x_368);
lean::cnstr_set(x_373, 1, x_370);
return x_373;
}
}
}
else
{
obj* x_385; obj* x_387; obj* x_389; obj* x_390; 
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
x_385 = lean::cnstr_get(x_50, 0);
x_387 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_389 = x_50;
} else {
 lean::inc(x_385);
 lean::inc(x_387);
 lean::dec(x_50);
 x_389 = lean::box(0);
}
if (lean::is_scalar(x_389)) {
 x_390 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_390 = x_389;
}
lean::cnstr_set(x_390, 0, x_385);
lean::cnstr_set(x_390, 1, x_387);
return x_390;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_391; obj* x_394; obj* x_395; 
x_391 = lean::cnstr_get(x_7, 0);
lean::inc(x_391);
lean::dec(x_7);
x_394 = lean::box(0);
x_395 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_395, 0, x_394);
lean::cnstr_set(x_395, 1, x_8);
x_5 = x_391;
x_6 = x_395;
goto _start;
}
else
{
obj* x_401; obj* x_404; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_401 = lean::cnstr_get(x_7, 0);
lean::inc(x_401);
lean::dec(x_7);
x_404 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_404, 0, x_401);
lean::cnstr_set(x_404, 1, x_8);
return x_404;
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
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
lean::inc(x_10);
x_16 = l_Lean_Parser_parseHeader(x_10);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::box(0);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
if (lean::obj_tag(x_17) == 0)
{
obj* x_25; obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::apply_2(x_2, x_25, x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 x_31 = x_28;
} else {
 lean::inc(x_29);
 lean::dec(x_28);
 x_31 = lean::box(0);
}
x_32 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_19;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_29);
return x_34;
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_4);
lean::dec(x_19);
x_37 = lean::cnstr_get(x_28, 0);
x_39 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_41 = x_28;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_28);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
else
{
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_54; 
x_43 = lean::cnstr_get(x_17, 0);
lean::inc(x_43);
lean::dec(x_17);
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_set(x_43, 0, lean::box(0));
 lean::cnstr_set(x_43, 1, lean::box(0));
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = l_List_reverse___rarg(x_48);
lean::inc(x_51);
lean::inc(x_2);
x_54 = l_List_mmap_x_27___main___at_Lean_runFrontend___spec__2(x_2, x_51, x_21);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_55 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_57 = x_54;
} else {
 lean::inc(x_55);
 lean::dec(x_54);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_20);
lean::cnstr_set(x_58, 1, x_55);
x_59 = lean::cnstr_get(x_10, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Expander_builtinTransformers;
lean::inc(x_64);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_67);
x_70 = lean::cnstr_get(x_64, 2);
lean::inc(x_70);
lean::dec(x_64);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_0);
lean::cnstr_set(x_73, 1, x_1);
lean::cnstr_set(x_73, 2, x_70);
lean::inc(x_10);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_10);
x_76 = l_Lean_runFrontend___closed__1;
lean::inc(x_75);
x_78 = l_Lean_Elaborator_mkState(x_75, x_4, x_76);
x_79 = lean::box(0);
if (lean::is_scalar(x_50)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_50;
}
lean::cnstr_set(x_80, 0, x_69);
lean::cnstr_set(x_80, 1, x_79);
if (lean::is_scalar(x_19)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_19;
}
lean::cnstr_set(x_81, 0, x_10);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_46);
lean::cnstr_set(x_83, 1, x_82);
x_84 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_2, x_3, x_51, x_75, x_79, x_83, x_58);
return x_84;
}
else
{
obj* x_94; obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_50);
lean::dec(x_51);
lean::dec(x_19);
lean::dec(x_46);
x_94 = lean::cnstr_get(x_54, 0);
x_96 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_98 = x_54;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_54);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_94);
lean::cnstr_set(x_99, 1, x_96);
return x_99;
}
}
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_104 = lean::cnstr_get(x_9, 0);
x_106 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_108 = x_9;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_9);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set(x_109, 1, x_106);
return x_109;
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
