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
obj* l_ioOfExcept___at_Lean_runFrontend___spec__1___boxed(obj*, obj*);
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
obj* l_Lean_mkConfig(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_tokens___rarg(x_3);
x_5 = l_Lean_Parser_command_builtinCommandParsers_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_tokens___rarg(x_5);
x_7 = l_List_append___rarg(x_4, x_6);
x_8 = l_Lean_Parser_Term_builtinLeadingParsers_Lean_Parser_HasTokens;
x_9 = l_Lean_Parser_tokens___rarg(x_8);
x_10 = l_List_append___rarg(x_7, x_9);
x_11 = l_Lean_Parser_Term_builtinTrailingParsers_Lean_Parser_HasTokens;
x_12 = l_Lean_Parser_tokens___rarg(x_11);
x_13 = l_List_append___rarg(x_10, x_12);
x_14 = l_Lean_Parser_mkTokenTrie(x_13);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
lean::dec(x_2);
lean::dec(x_1);
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_14);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_2);
x_20 = l_Lean_FileMap_fromString(x_2);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
x_23 = lean::box(0);
x_24 = l_Lean_Parser_Term_builtinLeadingParsers;
x_25 = l_Lean_Parser_Term_builtinTrailingParsers;
x_26 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_24);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set(x_26, 3, x_23);
lean::cnstr_set(x_26, 4, x_23);
x_27 = l_Lean_Parser_command_builtinCommandParsers;
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set(x_14, 0, x_28);
return x_14;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_29 = lean::cnstr_get(x_14, 0);
lean::inc(x_29);
lean::dec(x_14);
lean::inc(x_2);
x_30 = l_Lean_FileMap_fromString(x_2);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
x_33 = lean::box(0);
x_34 = l_Lean_Parser_Term_builtinLeadingParsers;
x_35 = l_Lean_Parser_Term_builtinTrailingParsers;
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_34);
lean::cnstr_set(x_36, 2, x_35);
lean::cnstr_set(x_36, 3, x_33);
lean::cnstr_set(x_36, 4, x_33);
x_37 = l_Lean_Parser_command_builtinCommandParsers;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
}
}
obj* l_ioOfExcept___at_Lean_runFrontend___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_2, 0);
lean::dec(x_5);
lean::inc(x_4);
lean::cnstr_set_tag(x_2, 1);
lean::cnstr_set(x_2, 0, x_4);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_2, 0);
lean::dec(x_11);
lean::inc(x_10);
lean::cnstr_set(x_2, 0, x_10);
return x_2;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_12, 0, x_15);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_2 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
lean::dec(x_11);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
x_23 = lean::cnstr_get(x_12, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_12, 0, x_15);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_2 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
lean::dec(x_11);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
x_23 = lean::cnstr_get(x_12, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_12, 0, x_15);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_2 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
lean::dec(x_11);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
x_23 = lean::cnstr_get(x_12, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
obj* l_List_mfor___main___at_Lean_runFrontend___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::cnstr_set(x_12, 0, x_15);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_2 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
lean::dec(x_11);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
x_23 = lean::cnstr_get(x_12, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseCommand(x_1, x_2);
return x_4;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_expand(x_1, x_2);
return x_4;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Elaborator_processCommand(x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("parsing");
return x_1;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expanding");
return x_1;
}
}
obj* _init_l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elaborating");
return x_1;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_17 = lean::cnstr_get(x_6, 1);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_6, 0);
lean::inc(x_20);
lean::dec(x_6);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
lean::dec(x_17);
x_22 = !lean::is_exclusive(x_18);
if (x_22 == 0)
{
obj* x_23; obj* x_24; uint8 x_25; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = lean::cnstr_get(x_18, 1);
lean::dec(x_24);
x_25 = !lean::is_exclusive(x_19);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_26 = lean::cnstr_get(x_19, 0);
x_27 = lean::cnstr_get(x_19, 1);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
lean::dec(x_28);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
lean::dec(x_29);
x_31 = lean::cnstr_get(x_30, 2);
lean::inc(x_31);
lean::dec(x_30);
x_32 = lean::cnstr_get(x_20, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
x_34 = l_Lean_FileMap_toPosition(x_31, x_33);
lean::dec(x_31);
lean::inc(x_23);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_35, 0, x_23);
lean::closure_set(x_35, 1, x_20);
x_36 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1;
x_37 = l_Lean_profileitPure___rarg(x_36, x_34, x_35, x_7);
if (lean::obj_tag(x_37) == 0)
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
x_40 = lean::box(0);
lean::cnstr_set(x_37, 0, x_40);
x_41 = lean::cnstr_get(x_39, 1);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
uint8 x_42; 
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
x_42 = !lean::is_exclusive(x_39);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
lean::dec(x_44);
x_45 = lean::cnstr_get(x_41, 0);
lean::inc(x_45);
lean::dec(x_41);
lean::inc(x_1);
x_46 = lean::apply_2(x_1, x_45, x_37);
if (lean::obj_tag(x_46) == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_46, 0);
lean::dec(x_48);
lean::cnstr_set(x_46, 0, x_40);
lean::inc(x_3);
lean::inc(x_1);
x_49 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_46);
if (lean::obj_tag(x_49) == 0)
{
if (x_2 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_43);
lean::dec(x_27);
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
lean::dec(x_49);
x_51 = lean::cnstr_get(x_21, 8);
lean::inc(x_51);
lean::dec(x_21);
lean::inc(x_5);
x_52 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_39, 1, x_51);
lean::cnstr_set(x_39, 0, x_52);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_39);
x_8 = x_53;
x_9 = x_50;
goto block_16;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_55 = lean::cnstr_get(x_21, 8);
lean::inc(x_55);
lean::dec(x_21);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_43);
lean::cnstr_set(x_56, 1, x_27);
x_57 = l_List_reverse___rarg(x_56);
lean::cnstr_set(x_39, 1, x_55);
lean::cnstr_set(x_39, 0, x_57);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_39);
x_8 = x_58;
x_9 = x_54;
goto block_16;
}
}
else
{
uint8 x_59; 
lean::free_heap_obj(x_39);
lean::dec(x_43);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_59 = !lean::is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get(x_49, 0);
x_61 = lean::cnstr_get(x_49, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_49);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_46, 1);
lean::inc(x_63);
lean::dec(x_46);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_40);
lean::cnstr_set(x_64, 1, x_63);
lean::inc(x_3);
lean::inc(x_1);
x_65 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_64);
if (lean::obj_tag(x_65) == 0)
{
if (x_2 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_43);
lean::dec(x_27);
x_66 = lean::cnstr_get(x_65, 1);
lean::inc(x_66);
lean::dec(x_65);
x_67 = lean::cnstr_get(x_21, 8);
lean::inc(x_67);
lean::dec(x_21);
lean::inc(x_5);
x_68 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_39, 1, x_67);
lean::cnstr_set(x_39, 0, x_68);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_39);
x_8 = x_69;
x_9 = x_66;
goto block_16;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::cnstr_get(x_65, 1);
lean::inc(x_70);
lean::dec(x_65);
x_71 = lean::cnstr_get(x_21, 8);
lean::inc(x_71);
lean::dec(x_21);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_43);
lean::cnstr_set(x_72, 1, x_27);
x_73 = l_List_reverse___rarg(x_72);
lean::cnstr_set(x_39, 1, x_71);
lean::cnstr_set(x_39, 0, x_73);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_39);
x_8 = x_74;
x_9 = x_70;
goto block_16;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::free_heap_obj(x_39);
lean::dec(x_43);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_75 = lean::cnstr_get(x_65, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_65, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_77 = x_65;
} else {
 lean::dec_ref(x_65);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8 x_79; 
lean::free_heap_obj(x_39);
lean::dec(x_43);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_79 = !lean::is_exclusive(x_46);
if (x_79 == 0)
{
return x_46;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_46, 0);
x_81 = lean::cnstr_get(x_46, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_46);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; 
x_83 = lean::cnstr_get(x_39, 0);
lean::inc(x_83);
lean::dec(x_39);
x_84 = lean::cnstr_get(x_41, 0);
lean::inc(x_84);
lean::dec(x_41);
lean::inc(x_1);
x_85 = lean::apply_2(x_1, x_84, x_37);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_86 = lean::cnstr_get(x_85, 1);
lean::inc(x_86);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_87 = x_85;
} else {
 lean::dec_ref(x_85);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_40);
lean::cnstr_set(x_88, 1, x_86);
lean::inc(x_3);
lean::inc(x_1);
x_89 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_88);
if (lean::obj_tag(x_89) == 0)
{
if (x_2 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_83);
lean::dec(x_27);
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
x_91 = lean::cnstr_get(x_21, 8);
lean::inc(x_91);
lean::dec(x_21);
lean::inc(x_5);
x_92 = l_List_reverse___rarg(x_5);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
x_8 = x_94;
x_9 = x_90;
goto block_16;
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_95 = lean::cnstr_get(x_89, 1);
lean::inc(x_95);
lean::dec(x_89);
x_96 = lean::cnstr_get(x_21, 8);
lean::inc(x_96);
lean::dec(x_21);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_83);
lean::cnstr_set(x_97, 1, x_27);
x_98 = l_List_reverse___rarg(x_97);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_96);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
x_8 = x_100;
x_9 = x_95;
goto block_16;
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_83);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_101 = lean::cnstr_get(x_89, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_89, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_103 = x_89;
} else {
 lean::dec_ref(x_89);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_83);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_105 = lean::cnstr_get(x_85, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_85, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_107 = x_85;
} else {
 lean::dec_ref(x_85);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
obj* x_109; uint8 x_110; 
x_109 = lean::cnstr_get(x_41, 0);
lean::inc(x_109);
lean::dec(x_41);
x_110 = !lean::is_exclusive(x_39);
if (x_110 == 0)
{
obj* x_111; obj* x_112; uint8 x_113; 
x_111 = lean::cnstr_get(x_39, 0);
x_112 = lean::cnstr_get(x_39, 1);
lean::dec(x_112);
x_113 = !lean::is_exclusive(x_109);
if (x_113 == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_109, 0);
x_115 = lean::cnstr_get(x_109, 1);
x_116 = l_List_reverse___rarg(x_115);
lean::inc(x_1);
x_117 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_116, x_37);
if (lean::obj_tag(x_117) == 0)
{
uint8 x_118; 
x_118 = !lean::is_exclusive(x_117);
if (x_118 == 0)
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_119 = lean::cnstr_get(x_117, 0);
lean::dec(x_119);
lean::cnstr_set(x_117, 0, x_40);
lean::inc(x_26);
lean::inc(x_111);
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_120, 0, x_111);
lean::closure_set(x_120, 1, x_26);
x_121 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_122 = l_Lean_profileitPure___rarg(x_121, x_34, x_120, x_117);
if (lean::obj_tag(x_122) == 0)
{
uint8 x_123; 
x_123 = !lean::is_exclusive(x_122);
if (x_123 == 0)
{
obj* x_124; 
x_124 = lean::cnstr_get(x_122, 0);
lean::cnstr_set(x_122, 0, x_40);
if (lean::obj_tag(x_124) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_111);
lean::dec(x_27);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
lean::dec(x_124);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_126 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_126, 0, x_18);
lean::inc(x_1);
x_127 = lean::apply_2(x_1, x_125, x_122);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; 
x_128 = lean::cnstr_get(x_127, 1);
lean::inc(x_128);
lean::dec(x_127);
x_8 = x_126;
x_9 = x_128;
goto block_16;
}
else
{
uint8 x_129; 
lean::dec(x_126);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_129 = !lean::is_exclusive(x_127);
if (x_129 == 0)
{
return x_127;
}
else
{
obj* x_130; obj* x_131; obj* x_132; 
x_130 = lean::cnstr_get(x_127, 0);
x_131 = lean::cnstr_get(x_127, 1);
lean::inc(x_131);
lean::inc(x_130);
lean::dec(x_127);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_133 = lean::cnstr_get(x_124, 0);
lean::inc(x_133);
lean::dec(x_124);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_111);
lean::cnstr_set(x_134, 1, x_27);
lean::cnstr_set(x_109, 1, x_134);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_135 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_135, 0, x_18);
lean::inc(x_1);
x_136 = lean::apply_2(x_1, x_133, x_122);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; 
x_137 = lean::cnstr_get(x_136, 1);
lean::inc(x_137);
lean::dec(x_136);
x_8 = x_135;
x_9 = x_137;
goto block_16;
}
else
{
uint8 x_138; 
lean::dec(x_135);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_138 = !lean::is_exclusive(x_136);
if (x_138 == 0)
{
return x_136;
}
else
{
obj* x_139; obj* x_140; obj* x_141; 
x_139 = lean::cnstr_get(x_136, 0);
x_140 = lean::cnstr_get(x_136, 1);
lean::inc(x_140);
lean::inc(x_139);
lean::dec(x_136);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_139);
lean::cnstr_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_26);
lean::dec(x_23);
x_142 = lean::cnstr_get(x_124, 0);
lean::inc(x_142);
lean::dec(x_124);
lean::inc(x_142);
lean::inc(x_4);
x_143 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_143, 0, x_4);
lean::closure_set(x_143, 1, x_21);
lean::closure_set(x_143, 2, x_142);
x_144 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_145 = l_Lean_profileitPure___rarg(x_144, x_34, x_143, x_122);
lean::dec(x_34);
if (lean::obj_tag(x_145) == 0)
{
uint8 x_146; 
x_146 = !lean::is_exclusive(x_145);
if (x_146 == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_147 = lean::cnstr_get(x_145, 0);
lean::cnstr_set(x_145, 0, x_40);
x_148 = lean::cnstr_get(x_147, 5);
lean::inc(x_148);
x_149 = l_List_reverse___rarg(x_148);
lean::inc(x_1);
x_150 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_149, x_145);
if (lean::obj_tag(x_150) == 0)
{
obj* x_151; obj* x_152; uint8 x_153; 
x_151 = lean::cnstr_get(x_150, 1);
lean::inc(x_151);
lean::dec(x_150);
x_152 = l_Lean_Parser_Module_eoi;
x_153 = l_Lean_Parser_Syntax_isOfKind___main(x_152, x_142);
lean::dec(x_142);
if (x_153 == 0)
{
if (x_2 == 0)
{
obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_111);
lean::dec(x_27);
x_154 = lean::cnstr_get(x_147, 6);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_147, 7);
lean::inc(x_155);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_155);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_154);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_147);
lean::cnstr_set(x_18, 0, x_114);
x_156 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_156, 0, x_18);
x_8 = x_156;
x_9 = x_151;
goto block_16;
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_157 = lean::cnstr_get(x_147, 6);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_147, 7);
lean::inc(x_158);
x_159 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_159, 0, x_111);
lean::cnstr_set(x_159, 1, x_27);
lean::cnstr_set(x_109, 1, x_159);
lean::cnstr_set(x_109, 0, x_158);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_157);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_147);
lean::cnstr_set(x_18, 0, x_114);
x_160 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_160, 0, x_18);
x_8 = x_160;
x_9 = x_151;
goto block_16;
}
}
else
{
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_111);
lean::dec(x_27);
x_161 = lean::cnstr_get(x_147, 8);
lean::inc(x_161);
lean::dec(x_147);
lean::inc(x_5);
x_162 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_109, 1, x_161);
lean::cnstr_set(x_109, 0, x_162);
x_163 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_163, 0, x_109);
x_8 = x_163;
x_9 = x_151;
goto block_16;
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_164 = lean::cnstr_get(x_147, 8);
lean::inc(x_164);
lean::dec(x_147);
x_165 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_165, 0, x_111);
lean::cnstr_set(x_165, 1, x_27);
x_166 = l_List_reverse___rarg(x_165);
lean::cnstr_set(x_109, 1, x_164);
lean::cnstr_set(x_109, 0, x_166);
x_167 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_167, 0, x_109);
x_8 = x_167;
x_9 = x_151;
goto block_16;
}
}
}
else
{
uint8 x_168; 
lean::dec(x_147);
lean::dec(x_142);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_168 = !lean::is_exclusive(x_150);
if (x_168 == 0)
{
return x_150;
}
else
{
obj* x_169; obj* x_170; obj* x_171; 
x_169 = lean::cnstr_get(x_150, 0);
x_170 = lean::cnstr_get(x_150, 1);
lean::inc(x_170);
lean::inc(x_169);
lean::dec(x_150);
x_171 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_172 = lean::cnstr_get(x_145, 0);
x_173 = lean::cnstr_get(x_145, 1);
lean::inc(x_173);
lean::inc(x_172);
lean::dec(x_145);
x_174 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_174, 0, x_40);
lean::cnstr_set(x_174, 1, x_173);
x_175 = lean::cnstr_get(x_172, 5);
lean::inc(x_175);
x_176 = l_List_reverse___rarg(x_175);
lean::inc(x_1);
x_177 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_176, x_174);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_179; uint8 x_180; 
x_178 = lean::cnstr_get(x_177, 1);
lean::inc(x_178);
lean::dec(x_177);
x_179 = l_Lean_Parser_Module_eoi;
x_180 = l_Lean_Parser_Syntax_isOfKind___main(x_179, x_142);
lean::dec(x_142);
if (x_180 == 0)
{
if (x_2 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_111);
lean::dec(x_27);
x_181 = lean::cnstr_get(x_172, 6);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_172, 7);
lean::inc(x_182);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_182);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_181);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_172);
lean::cnstr_set(x_18, 0, x_114);
x_183 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_183, 0, x_18);
x_8 = x_183;
x_9 = x_178;
goto block_16;
}
else
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_184 = lean::cnstr_get(x_172, 6);
lean::inc(x_184);
x_185 = lean::cnstr_get(x_172, 7);
lean::inc(x_185);
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_111);
lean::cnstr_set(x_186, 1, x_27);
lean::cnstr_set(x_109, 1, x_186);
lean::cnstr_set(x_109, 0, x_185);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_184);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_172);
lean::cnstr_set(x_18, 0, x_114);
x_187 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_187, 0, x_18);
x_8 = x_187;
x_9 = x_178;
goto block_16;
}
}
else
{
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_188; obj* x_189; obj* x_190; 
lean::dec(x_111);
lean::dec(x_27);
x_188 = lean::cnstr_get(x_172, 8);
lean::inc(x_188);
lean::dec(x_172);
lean::inc(x_5);
x_189 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_109, 1, x_188);
lean::cnstr_set(x_109, 0, x_189);
x_190 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_190, 0, x_109);
x_8 = x_190;
x_9 = x_178;
goto block_16;
}
else
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_191 = lean::cnstr_get(x_172, 8);
lean::inc(x_191);
lean::dec(x_172);
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_111);
lean::cnstr_set(x_192, 1, x_27);
x_193 = l_List_reverse___rarg(x_192);
lean::cnstr_set(x_109, 1, x_191);
lean::cnstr_set(x_109, 0, x_193);
x_194 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_194, 0, x_109);
x_8 = x_194;
x_9 = x_178;
goto block_16;
}
}
}
else
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_172);
lean::dec(x_142);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_195 = lean::cnstr_get(x_177, 0);
lean::inc(x_195);
x_196 = lean::cnstr_get(x_177, 1);
lean::inc(x_196);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_197 = x_177;
} else {
 lean::dec_ref(x_177);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_195);
lean::cnstr_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
uint8 x_199; 
lean::dec(x_142);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_199 = !lean::is_exclusive(x_145);
if (x_199 == 0)
{
return x_145;
}
else
{
obj* x_200; obj* x_201; obj* x_202; 
x_200 = lean::cnstr_get(x_145, 0);
x_201 = lean::cnstr_get(x_145, 1);
lean::inc(x_201);
lean::inc(x_200);
lean::dec(x_145);
x_202 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
obj* x_203; obj* x_204; obj* x_205; 
x_203 = lean::cnstr_get(x_122, 0);
x_204 = lean::cnstr_get(x_122, 1);
lean::inc(x_204);
lean::inc(x_203);
lean::dec(x_122);
x_205 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_205, 0, x_40);
lean::cnstr_set(x_205, 1, x_204);
if (lean::obj_tag(x_203) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_111);
lean::dec(x_27);
x_206 = lean::cnstr_get(x_203, 0);
lean::inc(x_206);
lean::dec(x_203);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_207 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_207, 0, x_18);
lean::inc(x_1);
x_208 = lean::apply_2(x_1, x_206, x_205);
if (lean::obj_tag(x_208) == 0)
{
obj* x_209; 
x_209 = lean::cnstr_get(x_208, 1);
lean::inc(x_209);
lean::dec(x_208);
x_8 = x_207;
x_9 = x_209;
goto block_16;
}
else
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_207);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_210 = lean::cnstr_get(x_208, 0);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 lean::cnstr_release(x_208, 1);
 x_212 = x_208;
} else {
 lean::dec_ref(x_208);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
lean::cnstr_set(x_213, 1, x_211);
return x_213;
}
}
else
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
x_214 = lean::cnstr_get(x_203, 0);
lean::inc(x_214);
lean::dec(x_203);
x_215 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_215, 0, x_111);
lean::cnstr_set(x_215, 1, x_27);
lean::cnstr_set(x_109, 1, x_215);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_216 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_216, 0, x_18);
lean::inc(x_1);
x_217 = lean::apply_2(x_1, x_214, x_205);
if (lean::obj_tag(x_217) == 0)
{
obj* x_218; 
x_218 = lean::cnstr_get(x_217, 1);
lean::inc(x_218);
lean::dec(x_217);
x_8 = x_216;
x_9 = x_218;
goto block_16;
}
else
{
obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_216);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_219 = lean::cnstr_get(x_217, 0);
lean::inc(x_219);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
if (lean::is_exclusive(x_217)) {
 lean::cnstr_release(x_217, 0);
 lean::cnstr_release(x_217, 1);
 x_221 = x_217;
} else {
 lean::dec_ref(x_217);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_219);
lean::cnstr_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_26);
lean::dec(x_23);
x_223 = lean::cnstr_get(x_203, 0);
lean::inc(x_223);
lean::dec(x_203);
lean::inc(x_223);
lean::inc(x_4);
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_224, 0, x_4);
lean::closure_set(x_224, 1, x_21);
lean::closure_set(x_224, 2, x_223);
x_225 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_226 = l_Lean_profileitPure___rarg(x_225, x_34, x_224, x_205);
lean::dec(x_34);
if (lean::obj_tag(x_226) == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_227 = lean::cnstr_get(x_226, 0);
lean::inc(x_227);
x_228 = lean::cnstr_get(x_226, 1);
lean::inc(x_228);
if (lean::is_exclusive(x_226)) {
 lean::cnstr_release(x_226, 0);
 lean::cnstr_release(x_226, 1);
 x_229 = x_226;
} else {
 lean::dec_ref(x_226);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_40);
lean::cnstr_set(x_230, 1, x_228);
x_231 = lean::cnstr_get(x_227, 5);
lean::inc(x_231);
x_232 = l_List_reverse___rarg(x_231);
lean::inc(x_1);
x_233 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_232, x_230);
if (lean::obj_tag(x_233) == 0)
{
obj* x_234; obj* x_235; uint8 x_236; 
x_234 = lean::cnstr_get(x_233, 1);
lean::inc(x_234);
lean::dec(x_233);
x_235 = l_Lean_Parser_Module_eoi;
x_236 = l_Lean_Parser_Syntax_isOfKind___main(x_235, x_223);
lean::dec(x_223);
if (x_236 == 0)
{
if (x_2 == 0)
{
obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_111);
lean::dec(x_27);
x_237 = lean::cnstr_get(x_227, 6);
lean::inc(x_237);
x_238 = lean::cnstr_get(x_227, 7);
lean::inc(x_238);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_238);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_237);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_227);
lean::cnstr_set(x_18, 0, x_114);
x_239 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_239, 0, x_18);
x_8 = x_239;
x_9 = x_234;
goto block_16;
}
else
{
obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
x_240 = lean::cnstr_get(x_227, 6);
lean::inc(x_240);
x_241 = lean::cnstr_get(x_227, 7);
lean::inc(x_241);
x_242 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_242, 0, x_111);
lean::cnstr_set(x_242, 1, x_27);
lean::cnstr_set(x_109, 1, x_242);
lean::cnstr_set(x_109, 0, x_241);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_240);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_227);
lean::cnstr_set(x_18, 0, x_114);
x_243 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_243, 0, x_18);
x_8 = x_243;
x_9 = x_234;
goto block_16;
}
}
else
{
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_111);
lean::dec(x_27);
x_244 = lean::cnstr_get(x_227, 8);
lean::inc(x_244);
lean::dec(x_227);
lean::inc(x_5);
x_245 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_109, 1, x_244);
lean::cnstr_set(x_109, 0, x_245);
x_246 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_246, 0, x_109);
x_8 = x_246;
x_9 = x_234;
goto block_16;
}
else
{
obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_247 = lean::cnstr_get(x_227, 8);
lean::inc(x_247);
lean::dec(x_227);
x_248 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_248, 0, x_111);
lean::cnstr_set(x_248, 1, x_27);
x_249 = l_List_reverse___rarg(x_248);
lean::cnstr_set(x_109, 1, x_247);
lean::cnstr_set(x_109, 0, x_249);
x_250 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_250, 0, x_109);
x_8 = x_250;
x_9 = x_234;
goto block_16;
}
}
}
else
{
obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_227);
lean::dec(x_223);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_251 = lean::cnstr_get(x_233, 0);
lean::inc(x_251);
x_252 = lean::cnstr_get(x_233, 1);
lean::inc(x_252);
if (lean::is_exclusive(x_233)) {
 lean::cnstr_release(x_233, 0);
 lean::cnstr_release(x_233, 1);
 x_253 = x_233;
} else {
 lean::dec_ref(x_233);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
lean::cnstr_set(x_254, 1, x_252);
return x_254;
}
}
else
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; 
lean::dec(x_223);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_255 = lean::cnstr_get(x_226, 0);
lean::inc(x_255);
x_256 = lean::cnstr_get(x_226, 1);
lean::inc(x_256);
if (lean::is_exclusive(x_226)) {
 lean::cnstr_release(x_226, 0);
 lean::cnstr_release(x_226, 1);
 x_257 = x_226;
} else {
 lean::dec_ref(x_226);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_256);
return x_258;
}
}
}
}
else
{
uint8 x_259; 
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_259 = !lean::is_exclusive(x_122);
if (x_259 == 0)
{
return x_122;
}
else
{
obj* x_260; obj* x_261; obj* x_262; 
x_260 = lean::cnstr_get(x_122, 0);
x_261 = lean::cnstr_get(x_122, 1);
lean::inc(x_261);
lean::inc(x_260);
lean::dec(x_122);
x_262 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_262, 0, x_260);
lean::cnstr_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; 
x_263 = lean::cnstr_get(x_117, 1);
lean::inc(x_263);
lean::dec(x_117);
x_264 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_264, 0, x_40);
lean::cnstr_set(x_264, 1, x_263);
lean::inc(x_26);
lean::inc(x_111);
x_265 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_265, 0, x_111);
lean::closure_set(x_265, 1, x_26);
x_266 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_267 = l_Lean_profileitPure___rarg(x_266, x_34, x_265, x_264);
if (lean::obj_tag(x_267) == 0)
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_268 = lean::cnstr_get(x_267, 0);
lean::inc(x_268);
x_269 = lean::cnstr_get(x_267, 1);
lean::inc(x_269);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 x_270 = x_267;
} else {
 lean::dec_ref(x_267);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_40);
lean::cnstr_set(x_271, 1, x_269);
if (lean::obj_tag(x_268) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_111);
lean::dec(x_27);
x_272 = lean::cnstr_get(x_268, 0);
lean::inc(x_272);
lean::dec(x_268);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_273 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_273, 0, x_18);
lean::inc(x_1);
x_274 = lean::apply_2(x_1, x_272, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
lean::dec(x_274);
x_8 = x_273;
x_9 = x_275;
goto block_16;
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
lean::dec(x_273);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_276 = lean::cnstr_get(x_274, 0);
lean::inc(x_276);
x_277 = lean::cnstr_get(x_274, 1);
lean::inc(x_277);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 lean::cnstr_release(x_274, 1);
 x_278 = x_274;
} else {
 lean::dec_ref(x_274);
 x_278 = lean::box(0);
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_276);
lean::cnstr_set(x_279, 1, x_277);
return x_279;
}
}
else
{
obj* x_280; obj* x_281; obj* x_282; obj* x_283; 
x_280 = lean::cnstr_get(x_268, 0);
lean::inc(x_280);
lean::dec(x_268);
x_281 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_281, 0, x_111);
lean::cnstr_set(x_281, 1, x_27);
lean::cnstr_set(x_109, 1, x_281);
lean::cnstr_set(x_109, 0, x_26);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_114);
x_282 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_282, 0, x_18);
lean::inc(x_1);
x_283 = lean::apply_2(x_1, x_280, x_271);
if (lean::obj_tag(x_283) == 0)
{
obj* x_284; 
x_284 = lean::cnstr_get(x_283, 1);
lean::inc(x_284);
lean::dec(x_283);
x_8 = x_282;
x_9 = x_284;
goto block_16;
}
else
{
obj* x_285; obj* x_286; obj* x_287; obj* x_288; 
lean::dec(x_282);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_285 = lean::cnstr_get(x_283, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_283, 1);
lean::inc(x_286);
if (lean::is_exclusive(x_283)) {
 lean::cnstr_release(x_283, 0);
 lean::cnstr_release(x_283, 1);
 x_287 = x_283;
} else {
 lean::dec_ref(x_283);
 x_287 = lean::box(0);
}
if (lean::is_scalar(x_287)) {
 x_288 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_288 = x_287;
}
lean::cnstr_set(x_288, 0, x_285);
lean::cnstr_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
lean::dec(x_26);
lean::dec(x_23);
x_289 = lean::cnstr_get(x_268, 0);
lean::inc(x_289);
lean::dec(x_268);
lean::inc(x_289);
lean::inc(x_4);
x_290 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_290, 0, x_4);
lean::closure_set(x_290, 1, x_21);
lean::closure_set(x_290, 2, x_289);
x_291 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_292 = l_Lean_profileitPure___rarg(x_291, x_34, x_290, x_271);
lean::dec(x_34);
if (lean::obj_tag(x_292) == 0)
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; 
x_293 = lean::cnstr_get(x_292, 0);
lean::inc(x_293);
x_294 = lean::cnstr_get(x_292, 1);
lean::inc(x_294);
if (lean::is_exclusive(x_292)) {
 lean::cnstr_release(x_292, 0);
 lean::cnstr_release(x_292, 1);
 x_295 = x_292;
} else {
 lean::dec_ref(x_292);
 x_295 = lean::box(0);
}
if (lean::is_scalar(x_295)) {
 x_296 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_296 = x_295;
}
lean::cnstr_set(x_296, 0, x_40);
lean::cnstr_set(x_296, 1, x_294);
x_297 = lean::cnstr_get(x_293, 5);
lean::inc(x_297);
x_298 = l_List_reverse___rarg(x_297);
lean::inc(x_1);
x_299 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_298, x_296);
if (lean::obj_tag(x_299) == 0)
{
obj* x_300; obj* x_301; uint8 x_302; 
x_300 = lean::cnstr_get(x_299, 1);
lean::inc(x_300);
lean::dec(x_299);
x_301 = l_Lean_Parser_Module_eoi;
x_302 = l_Lean_Parser_Syntax_isOfKind___main(x_301, x_289);
lean::dec(x_289);
if (x_302 == 0)
{
if (x_2 == 0)
{
obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_111);
lean::dec(x_27);
x_303 = lean::cnstr_get(x_293, 6);
lean::inc(x_303);
x_304 = lean::cnstr_get(x_293, 7);
lean::inc(x_304);
lean::inc(x_5);
lean::cnstr_set(x_109, 1, x_5);
lean::cnstr_set(x_109, 0, x_304);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_303);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_293);
lean::cnstr_set(x_18, 0, x_114);
x_305 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_305, 0, x_18);
x_8 = x_305;
x_9 = x_300;
goto block_16;
}
else
{
obj* x_306; obj* x_307; obj* x_308; obj* x_309; 
x_306 = lean::cnstr_get(x_293, 6);
lean::inc(x_306);
x_307 = lean::cnstr_get(x_293, 7);
lean::inc(x_307);
x_308 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_308, 0, x_111);
lean::cnstr_set(x_308, 1, x_27);
lean::cnstr_set(x_109, 1, x_308);
lean::cnstr_set(x_109, 0, x_307);
lean::cnstr_set(x_39, 1, x_109);
lean::cnstr_set(x_39, 0, x_306);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_293);
lean::cnstr_set(x_18, 0, x_114);
x_309 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_309, 0, x_18);
x_8 = x_309;
x_9 = x_300;
goto block_16;
}
}
else
{
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_111);
lean::dec(x_27);
x_310 = lean::cnstr_get(x_293, 8);
lean::inc(x_310);
lean::dec(x_293);
lean::inc(x_5);
x_311 = l_List_reverse___rarg(x_5);
lean::cnstr_set(x_109, 1, x_310);
lean::cnstr_set(x_109, 0, x_311);
x_312 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_312, 0, x_109);
x_8 = x_312;
x_9 = x_300;
goto block_16;
}
else
{
obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_313 = lean::cnstr_get(x_293, 8);
lean::inc(x_313);
lean::dec(x_293);
x_314 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_314, 0, x_111);
lean::cnstr_set(x_314, 1, x_27);
x_315 = l_List_reverse___rarg(x_314);
lean::cnstr_set(x_109, 1, x_313);
lean::cnstr_set(x_109, 0, x_315);
x_316 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_316, 0, x_109);
x_8 = x_316;
x_9 = x_300;
goto block_16;
}
}
}
else
{
obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
lean::dec(x_293);
lean::dec(x_289);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_317 = lean::cnstr_get(x_299, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_299, 1);
lean::inc(x_318);
if (lean::is_exclusive(x_299)) {
 lean::cnstr_release(x_299, 0);
 lean::cnstr_release(x_299, 1);
 x_319 = x_299;
} else {
 lean::dec_ref(x_299);
 x_319 = lean::box(0);
}
if (lean::is_scalar(x_319)) {
 x_320 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_320 = x_319;
}
lean::cnstr_set(x_320, 0, x_317);
lean::cnstr_set(x_320, 1, x_318);
return x_320;
}
}
else
{
obj* x_321; obj* x_322; obj* x_323; obj* x_324; 
lean::dec(x_289);
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_321 = lean::cnstr_get(x_292, 0);
lean::inc(x_321);
x_322 = lean::cnstr_get(x_292, 1);
lean::inc(x_322);
if (lean::is_exclusive(x_292)) {
 lean::cnstr_release(x_292, 0);
 lean::cnstr_release(x_292, 1);
 x_323 = x_292;
} else {
 lean::dec_ref(x_292);
 x_323 = lean::box(0);
}
if (lean::is_scalar(x_323)) {
 x_324 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_324 = x_323;
}
lean::cnstr_set(x_324, 0, x_321);
lean::cnstr_set(x_324, 1, x_322);
return x_324;
}
}
}
else
{
obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_325 = lean::cnstr_get(x_267, 0);
lean::inc(x_325);
x_326 = lean::cnstr_get(x_267, 1);
lean::inc(x_326);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 x_327 = x_267;
} else {
 lean::dec_ref(x_267);
 x_327 = lean::box(0);
}
if (lean::is_scalar(x_327)) {
 x_328 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_328 = x_327;
}
lean::cnstr_set(x_328, 0, x_325);
lean::cnstr_set(x_328, 1, x_326);
return x_328;
}
}
}
else
{
uint8 x_329; 
lean::free_heap_obj(x_109);
lean::dec(x_114);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_329 = !lean::is_exclusive(x_117);
if (x_329 == 0)
{
return x_117;
}
else
{
obj* x_330; obj* x_331; obj* x_332; 
x_330 = lean::cnstr_get(x_117, 0);
x_331 = lean::cnstr_get(x_117, 1);
lean::inc(x_331);
lean::inc(x_330);
lean::dec(x_117);
x_332 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_332, 0, x_330);
lean::cnstr_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_333 = lean::cnstr_get(x_109, 0);
x_334 = lean::cnstr_get(x_109, 1);
lean::inc(x_334);
lean::inc(x_333);
lean::dec(x_109);
x_335 = l_List_reverse___rarg(x_334);
lean::inc(x_1);
x_336 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_335, x_37);
if (lean::obj_tag(x_336) == 0)
{
obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
x_337 = lean::cnstr_get(x_336, 1);
lean::inc(x_337);
if (lean::is_exclusive(x_336)) {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 x_338 = x_336;
} else {
 lean::dec_ref(x_336);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_40);
lean::cnstr_set(x_339, 1, x_337);
lean::inc(x_26);
lean::inc(x_111);
x_340 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_340, 0, x_111);
lean::closure_set(x_340, 1, x_26);
x_341 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_342 = l_Lean_profileitPure___rarg(x_341, x_34, x_340, x_339);
if (lean::obj_tag(x_342) == 0)
{
obj* x_343; obj* x_344; obj* x_345; obj* x_346; 
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
x_344 = lean::cnstr_get(x_342, 1);
lean::inc(x_344);
if (lean::is_exclusive(x_342)) {
 lean::cnstr_release(x_342, 0);
 lean::cnstr_release(x_342, 1);
 x_345 = x_342;
} else {
 lean::dec_ref(x_342);
 x_345 = lean::box(0);
}
if (lean::is_scalar(x_345)) {
 x_346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_346 = x_345;
}
lean::cnstr_set(x_346, 0, x_40);
lean::cnstr_set(x_346, 1, x_344);
if (lean::obj_tag(x_343) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
lean::dec(x_111);
lean::dec(x_27);
x_347 = lean::cnstr_get(x_343, 0);
lean::inc(x_347);
lean::dec(x_343);
lean::inc(x_5);
x_348 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_348, 0, x_26);
lean::cnstr_set(x_348, 1, x_5);
lean::cnstr_set(x_39, 1, x_348);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_333);
x_349 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_349, 0, x_18);
lean::inc(x_1);
x_350 = lean::apply_2(x_1, x_347, x_346);
if (lean::obj_tag(x_350) == 0)
{
obj* x_351; 
x_351 = lean::cnstr_get(x_350, 1);
lean::inc(x_351);
lean::dec(x_350);
x_8 = x_349;
x_9 = x_351;
goto block_16;
}
else
{
obj* x_352; obj* x_353; obj* x_354; obj* x_355; 
lean::dec(x_349);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_352 = lean::cnstr_get(x_350, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_350, 1);
lean::inc(x_353);
if (lean::is_exclusive(x_350)) {
 lean::cnstr_release(x_350, 0);
 lean::cnstr_release(x_350, 1);
 x_354 = x_350;
} else {
 lean::dec_ref(x_350);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_352);
lean::cnstr_set(x_355, 1, x_353);
return x_355;
}
}
else
{
obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; 
x_356 = lean::cnstr_get(x_343, 0);
lean::inc(x_356);
lean::dec(x_343);
x_357 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_357, 0, x_111);
lean::cnstr_set(x_357, 1, x_27);
x_358 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_358, 0, x_26);
lean::cnstr_set(x_358, 1, x_357);
lean::cnstr_set(x_39, 1, x_358);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_333);
x_359 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_359, 0, x_18);
lean::inc(x_1);
x_360 = lean::apply_2(x_1, x_356, x_346);
if (lean::obj_tag(x_360) == 0)
{
obj* x_361; 
x_361 = lean::cnstr_get(x_360, 1);
lean::inc(x_361);
lean::dec(x_360);
x_8 = x_359;
x_9 = x_361;
goto block_16;
}
else
{
obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
lean::dec(x_359);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_362 = lean::cnstr_get(x_360, 0);
lean::inc(x_362);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
if (lean::is_exclusive(x_360)) {
 lean::cnstr_release(x_360, 0);
 lean::cnstr_release(x_360, 1);
 x_364 = x_360;
} else {
 lean::dec_ref(x_360);
 x_364 = lean::box(0);
}
if (lean::is_scalar(x_364)) {
 x_365 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_365 = x_364;
}
lean::cnstr_set(x_365, 0, x_362);
lean::cnstr_set(x_365, 1, x_363);
return x_365;
}
}
}
else
{
obj* x_366; obj* x_367; obj* x_368; obj* x_369; 
lean::dec(x_26);
lean::dec(x_23);
x_366 = lean::cnstr_get(x_343, 0);
lean::inc(x_366);
lean::dec(x_343);
lean::inc(x_366);
lean::inc(x_4);
x_367 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_367, 0, x_4);
lean::closure_set(x_367, 1, x_21);
lean::closure_set(x_367, 2, x_366);
x_368 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_369 = l_Lean_profileitPure___rarg(x_368, x_34, x_367, x_346);
lean::dec(x_34);
if (lean::obj_tag(x_369) == 0)
{
obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; 
x_370 = lean::cnstr_get(x_369, 0);
lean::inc(x_370);
x_371 = lean::cnstr_get(x_369, 1);
lean::inc(x_371);
if (lean::is_exclusive(x_369)) {
 lean::cnstr_release(x_369, 0);
 lean::cnstr_release(x_369, 1);
 x_372 = x_369;
} else {
 lean::dec_ref(x_369);
 x_372 = lean::box(0);
}
if (lean::is_scalar(x_372)) {
 x_373 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_373 = x_372;
}
lean::cnstr_set(x_373, 0, x_40);
lean::cnstr_set(x_373, 1, x_371);
x_374 = lean::cnstr_get(x_370, 5);
lean::inc(x_374);
x_375 = l_List_reverse___rarg(x_374);
lean::inc(x_1);
x_376 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_375, x_373);
if (lean::obj_tag(x_376) == 0)
{
obj* x_377; obj* x_378; uint8 x_379; 
x_377 = lean::cnstr_get(x_376, 1);
lean::inc(x_377);
lean::dec(x_376);
x_378 = l_Lean_Parser_Module_eoi;
x_379 = l_Lean_Parser_Syntax_isOfKind___main(x_378, x_366);
lean::dec(x_366);
if (x_379 == 0)
{
if (x_2 == 0)
{
obj* x_380; obj* x_381; obj* x_382; obj* x_383; 
lean::dec(x_111);
lean::dec(x_27);
x_380 = lean::cnstr_get(x_370, 6);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_370, 7);
lean::inc(x_381);
lean::inc(x_5);
x_382 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_5);
lean::cnstr_set(x_39, 1, x_382);
lean::cnstr_set(x_39, 0, x_380);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_370);
lean::cnstr_set(x_18, 0, x_333);
x_383 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_383, 0, x_18);
x_8 = x_383;
x_9 = x_377;
goto block_16;
}
else
{
obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; 
x_384 = lean::cnstr_get(x_370, 6);
lean::inc(x_384);
x_385 = lean::cnstr_get(x_370, 7);
lean::inc(x_385);
x_386 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_386, 0, x_111);
lean::cnstr_set(x_386, 1, x_27);
x_387 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_387, 0, x_385);
lean::cnstr_set(x_387, 1, x_386);
lean::cnstr_set(x_39, 1, x_387);
lean::cnstr_set(x_39, 0, x_384);
lean::cnstr_set(x_19, 1, x_39);
lean::cnstr_set(x_19, 0, x_370);
lean::cnstr_set(x_18, 0, x_333);
x_388 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_388, 0, x_18);
x_8 = x_388;
x_9 = x_377;
goto block_16;
}
}
else
{
lean::dec(x_333);
lean::free_heap_obj(x_39);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
lean::dec(x_111);
lean::dec(x_27);
x_389 = lean::cnstr_get(x_370, 8);
lean::inc(x_389);
lean::dec(x_370);
lean::inc(x_5);
x_390 = l_List_reverse___rarg(x_5);
x_391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_391, 0, x_390);
lean::cnstr_set(x_391, 1, x_389);
x_392 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_392, 0, x_391);
x_8 = x_392;
x_9 = x_377;
goto block_16;
}
else
{
obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
x_393 = lean::cnstr_get(x_370, 8);
lean::inc(x_393);
lean::dec(x_370);
x_394 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_394, 0, x_111);
lean::cnstr_set(x_394, 1, x_27);
x_395 = l_List_reverse___rarg(x_394);
x_396 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_396, 0, x_395);
lean::cnstr_set(x_396, 1, x_393);
x_397 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_397, 0, x_396);
x_8 = x_397;
x_9 = x_377;
goto block_16;
}
}
}
else
{
obj* x_398; obj* x_399; obj* x_400; obj* x_401; 
lean::dec(x_370);
lean::dec(x_366);
lean::dec(x_333);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_398 = lean::cnstr_get(x_376, 0);
lean::inc(x_398);
x_399 = lean::cnstr_get(x_376, 1);
lean::inc(x_399);
if (lean::is_exclusive(x_376)) {
 lean::cnstr_release(x_376, 0);
 lean::cnstr_release(x_376, 1);
 x_400 = x_376;
} else {
 lean::dec_ref(x_376);
 x_400 = lean::box(0);
}
if (lean::is_scalar(x_400)) {
 x_401 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_401 = x_400;
}
lean::cnstr_set(x_401, 0, x_398);
lean::cnstr_set(x_401, 1, x_399);
return x_401;
}
}
else
{
obj* x_402; obj* x_403; obj* x_404; obj* x_405; 
lean::dec(x_366);
lean::dec(x_333);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_402 = lean::cnstr_get(x_369, 0);
lean::inc(x_402);
x_403 = lean::cnstr_get(x_369, 1);
lean::inc(x_403);
if (lean::is_exclusive(x_369)) {
 lean::cnstr_release(x_369, 0);
 lean::cnstr_release(x_369, 1);
 x_404 = x_369;
} else {
 lean::dec_ref(x_369);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_402);
lean::cnstr_set(x_405, 1, x_403);
return x_405;
}
}
}
else
{
obj* x_406; obj* x_407; obj* x_408; obj* x_409; 
lean::dec(x_333);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_406 = lean::cnstr_get(x_342, 0);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_342, 1);
lean::inc(x_407);
if (lean::is_exclusive(x_342)) {
 lean::cnstr_release(x_342, 0);
 lean::cnstr_release(x_342, 1);
 x_408 = x_342;
} else {
 lean::dec_ref(x_342);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_406);
lean::cnstr_set(x_409, 1, x_407);
return x_409;
}
}
else
{
obj* x_410; obj* x_411; obj* x_412; obj* x_413; 
lean::dec(x_333);
lean::free_heap_obj(x_39);
lean::dec(x_111);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_410 = lean::cnstr_get(x_336, 0);
lean::inc(x_410);
x_411 = lean::cnstr_get(x_336, 1);
lean::inc(x_411);
if (lean::is_exclusive(x_336)) {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 x_412 = x_336;
} else {
 lean::dec_ref(x_336);
 x_412 = lean::box(0);
}
if (lean::is_scalar(x_412)) {
 x_413 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_413 = x_412;
}
lean::cnstr_set(x_413, 0, x_410);
lean::cnstr_set(x_413, 1, x_411);
return x_413;
}
}
}
else
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; 
x_414 = lean::cnstr_get(x_39, 0);
lean::inc(x_414);
lean::dec(x_39);
x_415 = lean::cnstr_get(x_109, 0);
lean::inc(x_415);
x_416 = lean::cnstr_get(x_109, 1);
lean::inc(x_416);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_417 = x_109;
} else {
 lean::dec_ref(x_109);
 x_417 = lean::box(0);
}
x_418 = l_List_reverse___rarg(x_416);
lean::inc(x_1);
x_419 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_418, x_37);
if (lean::obj_tag(x_419) == 0)
{
obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; obj* x_425; 
x_420 = lean::cnstr_get(x_419, 1);
lean::inc(x_420);
if (lean::is_exclusive(x_419)) {
 lean::cnstr_release(x_419, 0);
 lean::cnstr_release(x_419, 1);
 x_421 = x_419;
} else {
 lean::dec_ref(x_419);
 x_421 = lean::box(0);
}
if (lean::is_scalar(x_421)) {
 x_422 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_422 = x_421;
}
lean::cnstr_set(x_422, 0, x_40);
lean::cnstr_set(x_422, 1, x_420);
lean::inc(x_26);
lean::inc(x_414);
x_423 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_423, 0, x_414);
lean::closure_set(x_423, 1, x_26);
x_424 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_425 = l_Lean_profileitPure___rarg(x_424, x_34, x_423, x_422);
if (lean::obj_tag(x_425) == 0)
{
obj* x_426; obj* x_427; obj* x_428; obj* x_429; 
x_426 = lean::cnstr_get(x_425, 0);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_425, 1);
lean::inc(x_427);
if (lean::is_exclusive(x_425)) {
 lean::cnstr_release(x_425, 0);
 lean::cnstr_release(x_425, 1);
 x_428 = x_425;
} else {
 lean::dec_ref(x_425);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_40);
lean::cnstr_set(x_429, 1, x_427);
if (lean::obj_tag(x_426) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; 
lean::dec(x_414);
lean::dec(x_27);
x_430 = lean::cnstr_get(x_426, 0);
lean::inc(x_430);
lean::dec(x_426);
lean::inc(x_5);
if (lean::is_scalar(x_417)) {
 x_431 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_431 = x_417;
}
lean::cnstr_set(x_431, 0, x_26);
lean::cnstr_set(x_431, 1, x_5);
x_432 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_432, 0, x_23);
lean::cnstr_set(x_432, 1, x_431);
lean::cnstr_set(x_19, 1, x_432);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_415);
x_433 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_433, 0, x_18);
lean::inc(x_1);
x_434 = lean::apply_2(x_1, x_430, x_429);
if (lean::obj_tag(x_434) == 0)
{
obj* x_435; 
x_435 = lean::cnstr_get(x_434, 1);
lean::inc(x_435);
lean::dec(x_434);
x_8 = x_433;
x_9 = x_435;
goto block_16;
}
else
{
obj* x_436; obj* x_437; obj* x_438; obj* x_439; 
lean::dec(x_433);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_436 = lean::cnstr_get(x_434, 0);
lean::inc(x_436);
x_437 = lean::cnstr_get(x_434, 1);
lean::inc(x_437);
if (lean::is_exclusive(x_434)) {
 lean::cnstr_release(x_434, 0);
 lean::cnstr_release(x_434, 1);
 x_438 = x_434;
} else {
 lean::dec_ref(x_434);
 x_438 = lean::box(0);
}
if (lean::is_scalar(x_438)) {
 x_439 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_439 = x_438;
}
lean::cnstr_set(x_439, 0, x_436);
lean::cnstr_set(x_439, 1, x_437);
return x_439;
}
}
else
{
obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
x_440 = lean::cnstr_get(x_426, 0);
lean::inc(x_440);
lean::dec(x_426);
x_441 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_441, 0, x_414);
lean::cnstr_set(x_441, 1, x_27);
if (lean::is_scalar(x_417)) {
 x_442 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_442 = x_417;
}
lean::cnstr_set(x_442, 0, x_26);
lean::cnstr_set(x_442, 1, x_441);
x_443 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_443, 0, x_23);
lean::cnstr_set(x_443, 1, x_442);
lean::cnstr_set(x_19, 1, x_443);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_415);
x_444 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_444, 0, x_18);
lean::inc(x_1);
x_445 = lean::apply_2(x_1, x_440, x_429);
if (lean::obj_tag(x_445) == 0)
{
obj* x_446; 
x_446 = lean::cnstr_get(x_445, 1);
lean::inc(x_446);
lean::dec(x_445);
x_8 = x_444;
x_9 = x_446;
goto block_16;
}
else
{
obj* x_447; obj* x_448; obj* x_449; obj* x_450; 
lean::dec(x_444);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_447 = lean::cnstr_get(x_445, 0);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_445, 1);
lean::inc(x_448);
if (lean::is_exclusive(x_445)) {
 lean::cnstr_release(x_445, 0);
 lean::cnstr_release(x_445, 1);
 x_449 = x_445;
} else {
 lean::dec_ref(x_445);
 x_449 = lean::box(0);
}
if (lean::is_scalar(x_449)) {
 x_450 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_450 = x_449;
}
lean::cnstr_set(x_450, 0, x_447);
lean::cnstr_set(x_450, 1, x_448);
return x_450;
}
}
}
else
{
obj* x_451; obj* x_452; obj* x_453; obj* x_454; 
lean::dec(x_26);
lean::dec(x_23);
x_451 = lean::cnstr_get(x_426, 0);
lean::inc(x_451);
lean::dec(x_426);
lean::inc(x_451);
lean::inc(x_4);
x_452 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_452, 0, x_4);
lean::closure_set(x_452, 1, x_21);
lean::closure_set(x_452, 2, x_451);
x_453 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_454 = l_Lean_profileitPure___rarg(x_453, x_34, x_452, x_429);
lean::dec(x_34);
if (lean::obj_tag(x_454) == 0)
{
obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; 
x_455 = lean::cnstr_get(x_454, 0);
lean::inc(x_455);
x_456 = lean::cnstr_get(x_454, 1);
lean::inc(x_456);
if (lean::is_exclusive(x_454)) {
 lean::cnstr_release(x_454, 0);
 lean::cnstr_release(x_454, 1);
 x_457 = x_454;
} else {
 lean::dec_ref(x_454);
 x_457 = lean::box(0);
}
if (lean::is_scalar(x_457)) {
 x_458 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_458 = x_457;
}
lean::cnstr_set(x_458, 0, x_40);
lean::cnstr_set(x_458, 1, x_456);
x_459 = lean::cnstr_get(x_455, 5);
lean::inc(x_459);
x_460 = l_List_reverse___rarg(x_459);
lean::inc(x_1);
x_461 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_460, x_458);
if (lean::obj_tag(x_461) == 0)
{
obj* x_462; obj* x_463; uint8 x_464; 
x_462 = lean::cnstr_get(x_461, 1);
lean::inc(x_462);
lean::dec(x_461);
x_463 = l_Lean_Parser_Module_eoi;
x_464 = l_Lean_Parser_Syntax_isOfKind___main(x_463, x_451);
lean::dec(x_451);
if (x_464 == 0)
{
if (x_2 == 0)
{
obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
lean::dec(x_414);
lean::dec(x_27);
x_465 = lean::cnstr_get(x_455, 6);
lean::inc(x_465);
x_466 = lean::cnstr_get(x_455, 7);
lean::inc(x_466);
lean::inc(x_5);
if (lean::is_scalar(x_417)) {
 x_467 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_467 = x_417;
}
lean::cnstr_set(x_467, 0, x_466);
lean::cnstr_set(x_467, 1, x_5);
x_468 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_468, 0, x_465);
lean::cnstr_set(x_468, 1, x_467);
lean::cnstr_set(x_19, 1, x_468);
lean::cnstr_set(x_19, 0, x_455);
lean::cnstr_set(x_18, 0, x_415);
x_469 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_469, 0, x_18);
x_8 = x_469;
x_9 = x_462;
goto block_16;
}
else
{
obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; 
x_470 = lean::cnstr_get(x_455, 6);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_455, 7);
lean::inc(x_471);
x_472 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_472, 0, x_414);
lean::cnstr_set(x_472, 1, x_27);
if (lean::is_scalar(x_417)) {
 x_473 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_473 = x_417;
}
lean::cnstr_set(x_473, 0, x_471);
lean::cnstr_set(x_473, 1, x_472);
x_474 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_474, 0, x_470);
lean::cnstr_set(x_474, 1, x_473);
lean::cnstr_set(x_19, 1, x_474);
lean::cnstr_set(x_19, 0, x_455);
lean::cnstr_set(x_18, 0, x_415);
x_475 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_475, 0, x_18);
x_8 = x_475;
x_9 = x_462;
goto block_16;
}
}
else
{
lean::dec(x_415);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_476; obj* x_477; obj* x_478; obj* x_479; 
lean::dec(x_414);
lean::dec(x_27);
x_476 = lean::cnstr_get(x_455, 8);
lean::inc(x_476);
lean::dec(x_455);
lean::inc(x_5);
x_477 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_417)) {
 x_478 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_478 = x_417;
}
lean::cnstr_set(x_478, 0, x_477);
lean::cnstr_set(x_478, 1, x_476);
x_479 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_479, 0, x_478);
x_8 = x_479;
x_9 = x_462;
goto block_16;
}
else
{
obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; 
x_480 = lean::cnstr_get(x_455, 8);
lean::inc(x_480);
lean::dec(x_455);
x_481 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_481, 0, x_414);
lean::cnstr_set(x_481, 1, x_27);
x_482 = l_List_reverse___rarg(x_481);
if (lean::is_scalar(x_417)) {
 x_483 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_483 = x_417;
}
lean::cnstr_set(x_483, 0, x_482);
lean::cnstr_set(x_483, 1, x_480);
x_484 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_484, 0, x_483);
x_8 = x_484;
x_9 = x_462;
goto block_16;
}
}
}
else
{
obj* x_485; obj* x_486; obj* x_487; obj* x_488; 
lean::dec(x_455);
lean::dec(x_451);
lean::dec(x_417);
lean::dec(x_415);
lean::dec(x_414);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_485 = lean::cnstr_get(x_461, 0);
lean::inc(x_485);
x_486 = lean::cnstr_get(x_461, 1);
lean::inc(x_486);
if (lean::is_exclusive(x_461)) {
 lean::cnstr_release(x_461, 0);
 lean::cnstr_release(x_461, 1);
 x_487 = x_461;
} else {
 lean::dec_ref(x_461);
 x_487 = lean::box(0);
}
if (lean::is_scalar(x_487)) {
 x_488 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_488 = x_487;
}
lean::cnstr_set(x_488, 0, x_485);
lean::cnstr_set(x_488, 1, x_486);
return x_488;
}
}
else
{
obj* x_489; obj* x_490; obj* x_491; obj* x_492; 
lean::dec(x_451);
lean::dec(x_417);
lean::dec(x_415);
lean::dec(x_414);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_489 = lean::cnstr_get(x_454, 0);
lean::inc(x_489);
x_490 = lean::cnstr_get(x_454, 1);
lean::inc(x_490);
if (lean::is_exclusive(x_454)) {
 lean::cnstr_release(x_454, 0);
 lean::cnstr_release(x_454, 1);
 x_491 = x_454;
} else {
 lean::dec_ref(x_454);
 x_491 = lean::box(0);
}
if (lean::is_scalar(x_491)) {
 x_492 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_492 = x_491;
}
lean::cnstr_set(x_492, 0, x_489);
lean::cnstr_set(x_492, 1, x_490);
return x_492;
}
}
}
else
{
obj* x_493; obj* x_494; obj* x_495; obj* x_496; 
lean::dec(x_417);
lean::dec(x_415);
lean::dec(x_414);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_493 = lean::cnstr_get(x_425, 0);
lean::inc(x_493);
x_494 = lean::cnstr_get(x_425, 1);
lean::inc(x_494);
if (lean::is_exclusive(x_425)) {
 lean::cnstr_release(x_425, 0);
 lean::cnstr_release(x_425, 1);
 x_495 = x_425;
} else {
 lean::dec_ref(x_425);
 x_495 = lean::box(0);
}
if (lean::is_scalar(x_495)) {
 x_496 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_496 = x_495;
}
lean::cnstr_set(x_496, 0, x_493);
lean::cnstr_set(x_496, 1, x_494);
return x_496;
}
}
else
{
obj* x_497; obj* x_498; obj* x_499; obj* x_500; 
lean::dec(x_417);
lean::dec(x_415);
lean::dec(x_414);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_497 = lean::cnstr_get(x_419, 0);
lean::inc(x_497);
x_498 = lean::cnstr_get(x_419, 1);
lean::inc(x_498);
if (lean::is_exclusive(x_419)) {
 lean::cnstr_release(x_419, 0);
 lean::cnstr_release(x_419, 1);
 x_499 = x_419;
} else {
 lean::dec_ref(x_419);
 x_499 = lean::box(0);
}
if (lean::is_scalar(x_499)) {
 x_500 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_500 = x_499;
}
lean::cnstr_set(x_500, 0, x_497);
lean::cnstr_set(x_500, 1, x_498);
return x_500;
}
}
}
}
else
{
obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; 
x_501 = lean::cnstr_get(x_37, 0);
x_502 = lean::cnstr_get(x_37, 1);
lean::inc(x_502);
lean::inc(x_501);
lean::dec(x_37);
x_503 = lean::box(0);
x_504 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_504, 0, x_503);
lean::cnstr_set(x_504, 1, x_502);
x_505 = lean::cnstr_get(x_501, 1);
lean::inc(x_505);
if (lean::obj_tag(x_505) == 0)
{
obj* x_506; obj* x_507; obj* x_508; obj* x_509; 
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
x_506 = lean::cnstr_get(x_501, 0);
lean::inc(x_506);
if (lean::is_exclusive(x_501)) {
 lean::cnstr_release(x_501, 0);
 lean::cnstr_release(x_501, 1);
 x_507 = x_501;
} else {
 lean::dec_ref(x_501);
 x_507 = lean::box(0);
}
x_508 = lean::cnstr_get(x_505, 0);
lean::inc(x_508);
lean::dec(x_505);
lean::inc(x_1);
x_509 = lean::apply_2(x_1, x_508, x_504);
if (lean::obj_tag(x_509) == 0)
{
obj* x_510; obj* x_511; obj* x_512; obj* x_513; 
x_510 = lean::cnstr_get(x_509, 1);
lean::inc(x_510);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_release(x_509, 0);
 lean::cnstr_release(x_509, 1);
 x_511 = x_509;
} else {
 lean::dec_ref(x_509);
 x_511 = lean::box(0);
}
if (lean::is_scalar(x_511)) {
 x_512 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_512 = x_511;
}
lean::cnstr_set(x_512, 0, x_503);
lean::cnstr_set(x_512, 1, x_510);
lean::inc(x_3);
lean::inc(x_1);
x_513 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_512);
if (lean::obj_tag(x_513) == 0)
{
if (x_2 == 0)
{
obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; 
lean::dec(x_506);
lean::dec(x_27);
x_514 = lean::cnstr_get(x_513, 1);
lean::inc(x_514);
lean::dec(x_513);
x_515 = lean::cnstr_get(x_21, 8);
lean::inc(x_515);
lean::dec(x_21);
lean::inc(x_5);
x_516 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_507)) {
 x_517 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_517 = x_507;
}
lean::cnstr_set(x_517, 0, x_516);
lean::cnstr_set(x_517, 1, x_515);
x_518 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_518, 0, x_517);
x_8 = x_518;
x_9 = x_514;
goto block_16;
}
else
{
obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; 
x_519 = lean::cnstr_get(x_513, 1);
lean::inc(x_519);
lean::dec(x_513);
x_520 = lean::cnstr_get(x_21, 8);
lean::inc(x_520);
lean::dec(x_21);
x_521 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_521, 0, x_506);
lean::cnstr_set(x_521, 1, x_27);
x_522 = l_List_reverse___rarg(x_521);
if (lean::is_scalar(x_507)) {
 x_523 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_523 = x_507;
}
lean::cnstr_set(x_523, 0, x_522);
lean::cnstr_set(x_523, 1, x_520);
x_524 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_524, 0, x_523);
x_8 = x_524;
x_9 = x_519;
goto block_16;
}
}
else
{
obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_507);
lean::dec(x_506);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_525 = lean::cnstr_get(x_513, 0);
lean::inc(x_525);
x_526 = lean::cnstr_get(x_513, 1);
lean::inc(x_526);
if (lean::is_exclusive(x_513)) {
 lean::cnstr_release(x_513, 0);
 lean::cnstr_release(x_513, 1);
 x_527 = x_513;
} else {
 lean::dec_ref(x_513);
 x_527 = lean::box(0);
}
if (lean::is_scalar(x_527)) {
 x_528 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_528 = x_527;
}
lean::cnstr_set(x_528, 0, x_525);
lean::cnstr_set(x_528, 1, x_526);
return x_528;
}
}
else
{
obj* x_529; obj* x_530; obj* x_531; obj* x_532; 
lean::dec(x_507);
lean::dec(x_506);
lean::dec(x_27);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_529 = lean::cnstr_get(x_509, 0);
lean::inc(x_529);
x_530 = lean::cnstr_get(x_509, 1);
lean::inc(x_530);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_release(x_509, 0);
 lean::cnstr_release(x_509, 1);
 x_531 = x_509;
} else {
 lean::dec_ref(x_509);
 x_531 = lean::box(0);
}
if (lean::is_scalar(x_531)) {
 x_532 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_532 = x_531;
}
lean::cnstr_set(x_532, 0, x_529);
lean::cnstr_set(x_532, 1, x_530);
return x_532;
}
}
else
{
obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; 
x_533 = lean::cnstr_get(x_505, 0);
lean::inc(x_533);
lean::dec(x_505);
x_534 = lean::cnstr_get(x_501, 0);
lean::inc(x_534);
if (lean::is_exclusive(x_501)) {
 lean::cnstr_release(x_501, 0);
 lean::cnstr_release(x_501, 1);
 x_535 = x_501;
} else {
 lean::dec_ref(x_501);
 x_535 = lean::box(0);
}
x_536 = lean::cnstr_get(x_533, 0);
lean::inc(x_536);
x_537 = lean::cnstr_get(x_533, 1);
lean::inc(x_537);
if (lean::is_exclusive(x_533)) {
 lean::cnstr_release(x_533, 0);
 lean::cnstr_release(x_533, 1);
 x_538 = x_533;
} else {
 lean::dec_ref(x_533);
 x_538 = lean::box(0);
}
x_539 = l_List_reverse___rarg(x_537);
lean::inc(x_1);
x_540 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_539, x_504);
if (lean::obj_tag(x_540) == 0)
{
obj* x_541; obj* x_542; obj* x_543; obj* x_544; obj* x_545; obj* x_546; 
x_541 = lean::cnstr_get(x_540, 1);
lean::inc(x_541);
if (lean::is_exclusive(x_540)) {
 lean::cnstr_release(x_540, 0);
 lean::cnstr_release(x_540, 1);
 x_542 = x_540;
} else {
 lean::dec_ref(x_540);
 x_542 = lean::box(0);
}
if (lean::is_scalar(x_542)) {
 x_543 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_543 = x_542;
}
lean::cnstr_set(x_543, 0, x_503);
lean::cnstr_set(x_543, 1, x_541);
lean::inc(x_26);
lean::inc(x_534);
x_544 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_544, 0, x_534);
lean::closure_set(x_544, 1, x_26);
x_545 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_546 = l_Lean_profileitPure___rarg(x_545, x_34, x_544, x_543);
if (lean::obj_tag(x_546) == 0)
{
obj* x_547; obj* x_548; obj* x_549; obj* x_550; 
x_547 = lean::cnstr_get(x_546, 0);
lean::inc(x_547);
x_548 = lean::cnstr_get(x_546, 1);
lean::inc(x_548);
if (lean::is_exclusive(x_546)) {
 lean::cnstr_release(x_546, 0);
 lean::cnstr_release(x_546, 1);
 x_549 = x_546;
} else {
 lean::dec_ref(x_546);
 x_549 = lean::box(0);
}
if (lean::is_scalar(x_549)) {
 x_550 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_550 = x_549;
}
lean::cnstr_set(x_550, 0, x_503);
lean::cnstr_set(x_550, 1, x_548);
if (lean::obj_tag(x_547) == 0)
{
lean::dec(x_34);
if (x_2 == 0)
{
obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; 
lean::dec(x_534);
lean::dec(x_27);
x_551 = lean::cnstr_get(x_547, 0);
lean::inc(x_551);
lean::dec(x_547);
lean::inc(x_5);
if (lean::is_scalar(x_538)) {
 x_552 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_552 = x_538;
}
lean::cnstr_set(x_552, 0, x_26);
lean::cnstr_set(x_552, 1, x_5);
if (lean::is_scalar(x_535)) {
 x_553 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_553 = x_535;
}
lean::cnstr_set(x_553, 0, x_23);
lean::cnstr_set(x_553, 1, x_552);
lean::cnstr_set(x_19, 1, x_553);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_536);
x_554 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_554, 0, x_18);
lean::inc(x_1);
x_555 = lean::apply_2(x_1, x_551, x_550);
if (lean::obj_tag(x_555) == 0)
{
obj* x_556; 
x_556 = lean::cnstr_get(x_555, 1);
lean::inc(x_556);
lean::dec(x_555);
x_8 = x_554;
x_9 = x_556;
goto block_16;
}
else
{
obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
lean::dec(x_554);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_557 = lean::cnstr_get(x_555, 0);
lean::inc(x_557);
x_558 = lean::cnstr_get(x_555, 1);
lean::inc(x_558);
if (lean::is_exclusive(x_555)) {
 lean::cnstr_release(x_555, 0);
 lean::cnstr_release(x_555, 1);
 x_559 = x_555;
} else {
 lean::dec_ref(x_555);
 x_559 = lean::box(0);
}
if (lean::is_scalar(x_559)) {
 x_560 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_560 = x_559;
}
lean::cnstr_set(x_560, 0, x_557);
lean::cnstr_set(x_560, 1, x_558);
return x_560;
}
}
else
{
obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; 
x_561 = lean::cnstr_get(x_547, 0);
lean::inc(x_561);
lean::dec(x_547);
x_562 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_562, 0, x_534);
lean::cnstr_set(x_562, 1, x_27);
if (lean::is_scalar(x_538)) {
 x_563 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_563 = x_538;
}
lean::cnstr_set(x_563, 0, x_26);
lean::cnstr_set(x_563, 1, x_562);
if (lean::is_scalar(x_535)) {
 x_564 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_564 = x_535;
}
lean::cnstr_set(x_564, 0, x_23);
lean::cnstr_set(x_564, 1, x_563);
lean::cnstr_set(x_19, 1, x_564);
lean::cnstr_set(x_19, 0, x_21);
lean::cnstr_set(x_18, 0, x_536);
x_565 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_565, 0, x_18);
lean::inc(x_1);
x_566 = lean::apply_2(x_1, x_561, x_550);
if (lean::obj_tag(x_566) == 0)
{
obj* x_567; 
x_567 = lean::cnstr_get(x_566, 1);
lean::inc(x_567);
lean::dec(x_566);
x_8 = x_565;
x_9 = x_567;
goto block_16;
}
else
{
obj* x_568; obj* x_569; obj* x_570; obj* x_571; 
lean::dec(x_565);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_568 = lean::cnstr_get(x_566, 0);
lean::inc(x_568);
x_569 = lean::cnstr_get(x_566, 1);
lean::inc(x_569);
if (lean::is_exclusive(x_566)) {
 lean::cnstr_release(x_566, 0);
 lean::cnstr_release(x_566, 1);
 x_570 = x_566;
} else {
 lean::dec_ref(x_566);
 x_570 = lean::box(0);
}
if (lean::is_scalar(x_570)) {
 x_571 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_571 = x_570;
}
lean::cnstr_set(x_571, 0, x_568);
lean::cnstr_set(x_571, 1, x_569);
return x_571;
}
}
}
else
{
obj* x_572; obj* x_573; obj* x_574; obj* x_575; 
lean::dec(x_26);
lean::dec(x_23);
x_572 = lean::cnstr_get(x_547, 0);
lean::inc(x_572);
lean::dec(x_547);
lean::inc(x_572);
lean::inc(x_4);
x_573 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_573, 0, x_4);
lean::closure_set(x_573, 1, x_21);
lean::closure_set(x_573, 2, x_572);
x_574 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_575 = l_Lean_profileitPure___rarg(x_574, x_34, x_573, x_550);
lean::dec(x_34);
if (lean::obj_tag(x_575) == 0)
{
obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; 
x_576 = lean::cnstr_get(x_575, 0);
lean::inc(x_576);
x_577 = lean::cnstr_get(x_575, 1);
lean::inc(x_577);
if (lean::is_exclusive(x_575)) {
 lean::cnstr_release(x_575, 0);
 lean::cnstr_release(x_575, 1);
 x_578 = x_575;
} else {
 lean::dec_ref(x_575);
 x_578 = lean::box(0);
}
if (lean::is_scalar(x_578)) {
 x_579 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_579 = x_578;
}
lean::cnstr_set(x_579, 0, x_503);
lean::cnstr_set(x_579, 1, x_577);
x_580 = lean::cnstr_get(x_576, 5);
lean::inc(x_580);
x_581 = l_List_reverse___rarg(x_580);
lean::inc(x_1);
x_582 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_581, x_579);
if (lean::obj_tag(x_582) == 0)
{
obj* x_583; obj* x_584; uint8 x_585; 
x_583 = lean::cnstr_get(x_582, 1);
lean::inc(x_583);
lean::dec(x_582);
x_584 = l_Lean_Parser_Module_eoi;
x_585 = l_Lean_Parser_Syntax_isOfKind___main(x_584, x_572);
lean::dec(x_572);
if (x_585 == 0)
{
if (x_2 == 0)
{
obj* x_586; obj* x_587; obj* x_588; obj* x_589; obj* x_590; 
lean::dec(x_534);
lean::dec(x_27);
x_586 = lean::cnstr_get(x_576, 6);
lean::inc(x_586);
x_587 = lean::cnstr_get(x_576, 7);
lean::inc(x_587);
lean::inc(x_5);
if (lean::is_scalar(x_538)) {
 x_588 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_588 = x_538;
}
lean::cnstr_set(x_588, 0, x_587);
lean::cnstr_set(x_588, 1, x_5);
if (lean::is_scalar(x_535)) {
 x_589 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_589 = x_535;
}
lean::cnstr_set(x_589, 0, x_586);
lean::cnstr_set(x_589, 1, x_588);
lean::cnstr_set(x_19, 1, x_589);
lean::cnstr_set(x_19, 0, x_576);
lean::cnstr_set(x_18, 0, x_536);
x_590 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_590, 0, x_18);
x_8 = x_590;
x_9 = x_583;
goto block_16;
}
else
{
obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; 
x_591 = lean::cnstr_get(x_576, 6);
lean::inc(x_591);
x_592 = lean::cnstr_get(x_576, 7);
lean::inc(x_592);
x_593 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_593, 0, x_534);
lean::cnstr_set(x_593, 1, x_27);
if (lean::is_scalar(x_538)) {
 x_594 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_594 = x_538;
}
lean::cnstr_set(x_594, 0, x_592);
lean::cnstr_set(x_594, 1, x_593);
if (lean::is_scalar(x_535)) {
 x_595 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_595 = x_535;
}
lean::cnstr_set(x_595, 0, x_591);
lean::cnstr_set(x_595, 1, x_594);
lean::cnstr_set(x_19, 1, x_595);
lean::cnstr_set(x_19, 0, x_576);
lean::cnstr_set(x_18, 0, x_536);
x_596 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_596, 0, x_18);
x_8 = x_596;
x_9 = x_583;
goto block_16;
}
}
else
{
lean::dec(x_536);
lean::dec(x_535);
lean::free_heap_obj(x_19);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
lean::dec(x_534);
lean::dec(x_27);
x_597 = lean::cnstr_get(x_576, 8);
lean::inc(x_597);
lean::dec(x_576);
lean::inc(x_5);
x_598 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_538)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_538;
}
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_597);
x_600 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_600, 0, x_599);
x_8 = x_600;
x_9 = x_583;
goto block_16;
}
else
{
obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; 
x_601 = lean::cnstr_get(x_576, 8);
lean::inc(x_601);
lean::dec(x_576);
x_602 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_602, 0, x_534);
lean::cnstr_set(x_602, 1, x_27);
x_603 = l_List_reverse___rarg(x_602);
if (lean::is_scalar(x_538)) {
 x_604 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_604 = x_538;
}
lean::cnstr_set(x_604, 0, x_603);
lean::cnstr_set(x_604, 1, x_601);
x_605 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_605, 0, x_604);
x_8 = x_605;
x_9 = x_583;
goto block_16;
}
}
}
else
{
obj* x_606; obj* x_607; obj* x_608; obj* x_609; 
lean::dec(x_576);
lean::dec(x_572);
lean::dec(x_538);
lean::dec(x_536);
lean::dec(x_535);
lean::dec(x_534);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_606 = lean::cnstr_get(x_582, 0);
lean::inc(x_606);
x_607 = lean::cnstr_get(x_582, 1);
lean::inc(x_607);
if (lean::is_exclusive(x_582)) {
 lean::cnstr_release(x_582, 0);
 lean::cnstr_release(x_582, 1);
 x_608 = x_582;
} else {
 lean::dec_ref(x_582);
 x_608 = lean::box(0);
}
if (lean::is_scalar(x_608)) {
 x_609 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_609 = x_608;
}
lean::cnstr_set(x_609, 0, x_606);
lean::cnstr_set(x_609, 1, x_607);
return x_609;
}
}
else
{
obj* x_610; obj* x_611; obj* x_612; obj* x_613; 
lean::dec(x_572);
lean::dec(x_538);
lean::dec(x_536);
lean::dec(x_535);
lean::dec(x_534);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_610 = lean::cnstr_get(x_575, 0);
lean::inc(x_610);
x_611 = lean::cnstr_get(x_575, 1);
lean::inc(x_611);
if (lean::is_exclusive(x_575)) {
 lean::cnstr_release(x_575, 0);
 lean::cnstr_release(x_575, 1);
 x_612 = x_575;
} else {
 lean::dec_ref(x_575);
 x_612 = lean::box(0);
}
if (lean::is_scalar(x_612)) {
 x_613 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_613 = x_612;
}
lean::cnstr_set(x_613, 0, x_610);
lean::cnstr_set(x_613, 1, x_611);
return x_613;
}
}
}
else
{
obj* x_614; obj* x_615; obj* x_616; obj* x_617; 
lean::dec(x_538);
lean::dec(x_536);
lean::dec(x_535);
lean::dec(x_534);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_614 = lean::cnstr_get(x_546, 0);
lean::inc(x_614);
x_615 = lean::cnstr_get(x_546, 1);
lean::inc(x_615);
if (lean::is_exclusive(x_546)) {
 lean::cnstr_release(x_546, 0);
 lean::cnstr_release(x_546, 1);
 x_616 = x_546;
} else {
 lean::dec_ref(x_546);
 x_616 = lean::box(0);
}
if (lean::is_scalar(x_616)) {
 x_617 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_617 = x_616;
}
lean::cnstr_set(x_617, 0, x_614);
lean::cnstr_set(x_617, 1, x_615);
return x_617;
}
}
else
{
obj* x_618; obj* x_619; obj* x_620; obj* x_621; 
lean::dec(x_538);
lean::dec(x_536);
lean::dec(x_535);
lean::dec(x_534);
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_618 = lean::cnstr_get(x_540, 0);
lean::inc(x_618);
x_619 = lean::cnstr_get(x_540, 1);
lean::inc(x_619);
if (lean::is_exclusive(x_540)) {
 lean::cnstr_release(x_540, 0);
 lean::cnstr_release(x_540, 1);
 x_620 = x_540;
} else {
 lean::dec_ref(x_540);
 x_620 = lean::box(0);
}
if (lean::is_scalar(x_620)) {
 x_621 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_621 = x_620;
}
lean::cnstr_set(x_621, 0, x_618);
lean::cnstr_set(x_621, 1, x_619);
return x_621;
}
}
}
}
else
{
uint8 x_622; 
lean::dec(x_34);
lean::free_heap_obj(x_19);
lean::dec(x_27);
lean::dec(x_26);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_622 = !lean::is_exclusive(x_37);
if (x_622 == 0)
{
return x_37;
}
else
{
obj* x_623; obj* x_624; obj* x_625; 
x_623 = lean::cnstr_get(x_37, 0);
x_624 = lean::cnstr_get(x_37, 1);
lean::inc(x_624);
lean::inc(x_623);
lean::dec(x_37);
x_625 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_625, 0, x_623);
lean::cnstr_set(x_625, 1, x_624);
return x_625;
}
}
}
else
{
obj* x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_636; obj* x_637; 
x_626 = lean::cnstr_get(x_19, 0);
x_627 = lean::cnstr_get(x_19, 1);
lean::inc(x_627);
lean::inc(x_626);
lean::dec(x_19);
x_628 = lean::cnstr_get(x_23, 0);
lean::inc(x_628);
x_629 = lean::cnstr_get(x_628, 0);
lean::inc(x_629);
lean::dec(x_628);
x_630 = lean::cnstr_get(x_629, 0);
lean::inc(x_630);
lean::dec(x_629);
x_631 = lean::cnstr_get(x_630, 2);
lean::inc(x_631);
lean::dec(x_630);
x_632 = lean::cnstr_get(x_20, 0);
lean::inc(x_632);
x_633 = lean::cnstr_get(x_632, 1);
lean::inc(x_633);
lean::dec(x_632);
x_634 = l_Lean_FileMap_toPosition(x_631, x_633);
lean::dec(x_631);
lean::inc(x_23);
x_635 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_635, 0, x_23);
lean::closure_set(x_635, 1, x_20);
x_636 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1;
x_637 = l_Lean_profileitPure___rarg(x_636, x_634, x_635, x_7);
if (lean::obj_tag(x_637) == 0)
{
obj* x_638; obj* x_639; obj* x_640; obj* x_641; obj* x_642; obj* x_643; 
x_638 = lean::cnstr_get(x_637, 0);
lean::inc(x_638);
x_639 = lean::cnstr_get(x_637, 1);
lean::inc(x_639);
if (lean::is_exclusive(x_637)) {
 lean::cnstr_release(x_637, 0);
 lean::cnstr_release(x_637, 1);
 x_640 = x_637;
} else {
 lean::dec_ref(x_637);
 x_640 = lean::box(0);
}
x_641 = lean::box(0);
if (lean::is_scalar(x_640)) {
 x_642 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_642 = x_640;
}
lean::cnstr_set(x_642, 0, x_641);
lean::cnstr_set(x_642, 1, x_639);
x_643 = lean::cnstr_get(x_638, 1);
lean::inc(x_643);
if (lean::obj_tag(x_643) == 0)
{
obj* x_644; obj* x_645; obj* x_646; obj* x_647; 
lean::dec(x_634);
lean::dec(x_626);
lean::free_heap_obj(x_18);
lean::dec(x_23);
x_644 = lean::cnstr_get(x_638, 0);
lean::inc(x_644);
if (lean::is_exclusive(x_638)) {
 lean::cnstr_release(x_638, 0);
 lean::cnstr_release(x_638, 1);
 x_645 = x_638;
} else {
 lean::dec_ref(x_638);
 x_645 = lean::box(0);
}
x_646 = lean::cnstr_get(x_643, 0);
lean::inc(x_646);
lean::dec(x_643);
lean::inc(x_1);
x_647 = lean::apply_2(x_1, x_646, x_642);
if (lean::obj_tag(x_647) == 0)
{
obj* x_648; obj* x_649; obj* x_650; obj* x_651; 
x_648 = lean::cnstr_get(x_647, 1);
lean::inc(x_648);
if (lean::is_exclusive(x_647)) {
 lean::cnstr_release(x_647, 0);
 lean::cnstr_release(x_647, 1);
 x_649 = x_647;
} else {
 lean::dec_ref(x_647);
 x_649 = lean::box(0);
}
if (lean::is_scalar(x_649)) {
 x_650 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_650 = x_649;
}
lean::cnstr_set(x_650, 0, x_641);
lean::cnstr_set(x_650, 1, x_648);
lean::inc(x_3);
lean::inc(x_1);
x_651 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_650);
if (lean::obj_tag(x_651) == 0)
{
if (x_2 == 0)
{
obj* x_652; obj* x_653; obj* x_654; obj* x_655; obj* x_656; 
lean::dec(x_644);
lean::dec(x_627);
x_652 = lean::cnstr_get(x_651, 1);
lean::inc(x_652);
lean::dec(x_651);
x_653 = lean::cnstr_get(x_21, 8);
lean::inc(x_653);
lean::dec(x_21);
lean::inc(x_5);
x_654 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_645)) {
 x_655 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_655 = x_645;
}
lean::cnstr_set(x_655, 0, x_654);
lean::cnstr_set(x_655, 1, x_653);
x_656 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_656, 0, x_655);
x_8 = x_656;
x_9 = x_652;
goto block_16;
}
else
{
obj* x_657; obj* x_658; obj* x_659; obj* x_660; obj* x_661; obj* x_662; 
x_657 = lean::cnstr_get(x_651, 1);
lean::inc(x_657);
lean::dec(x_651);
x_658 = lean::cnstr_get(x_21, 8);
lean::inc(x_658);
lean::dec(x_21);
x_659 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_659, 0, x_644);
lean::cnstr_set(x_659, 1, x_627);
x_660 = l_List_reverse___rarg(x_659);
if (lean::is_scalar(x_645)) {
 x_661 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_661 = x_645;
}
lean::cnstr_set(x_661, 0, x_660);
lean::cnstr_set(x_661, 1, x_658);
x_662 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_662, 0, x_661);
x_8 = x_662;
x_9 = x_657;
goto block_16;
}
}
else
{
obj* x_663; obj* x_664; obj* x_665; obj* x_666; 
lean::dec(x_645);
lean::dec(x_644);
lean::dec(x_627);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_663 = lean::cnstr_get(x_651, 0);
lean::inc(x_663);
x_664 = lean::cnstr_get(x_651, 1);
lean::inc(x_664);
if (lean::is_exclusive(x_651)) {
 lean::cnstr_release(x_651, 0);
 lean::cnstr_release(x_651, 1);
 x_665 = x_651;
} else {
 lean::dec_ref(x_651);
 x_665 = lean::box(0);
}
if (lean::is_scalar(x_665)) {
 x_666 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_666 = x_665;
}
lean::cnstr_set(x_666, 0, x_663);
lean::cnstr_set(x_666, 1, x_664);
return x_666;
}
}
else
{
obj* x_667; obj* x_668; obj* x_669; obj* x_670; 
lean::dec(x_645);
lean::dec(x_644);
lean::dec(x_627);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_667 = lean::cnstr_get(x_647, 0);
lean::inc(x_667);
x_668 = lean::cnstr_get(x_647, 1);
lean::inc(x_668);
if (lean::is_exclusive(x_647)) {
 lean::cnstr_release(x_647, 0);
 lean::cnstr_release(x_647, 1);
 x_669 = x_647;
} else {
 lean::dec_ref(x_647);
 x_669 = lean::box(0);
}
if (lean::is_scalar(x_669)) {
 x_670 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_670 = x_669;
}
lean::cnstr_set(x_670, 0, x_667);
lean::cnstr_set(x_670, 1, x_668);
return x_670;
}
}
else
{
obj* x_671; obj* x_672; obj* x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; 
x_671 = lean::cnstr_get(x_643, 0);
lean::inc(x_671);
lean::dec(x_643);
x_672 = lean::cnstr_get(x_638, 0);
lean::inc(x_672);
if (lean::is_exclusive(x_638)) {
 lean::cnstr_release(x_638, 0);
 lean::cnstr_release(x_638, 1);
 x_673 = x_638;
} else {
 lean::dec_ref(x_638);
 x_673 = lean::box(0);
}
x_674 = lean::cnstr_get(x_671, 0);
lean::inc(x_674);
x_675 = lean::cnstr_get(x_671, 1);
lean::inc(x_675);
if (lean::is_exclusive(x_671)) {
 lean::cnstr_release(x_671, 0);
 lean::cnstr_release(x_671, 1);
 x_676 = x_671;
} else {
 lean::dec_ref(x_671);
 x_676 = lean::box(0);
}
x_677 = l_List_reverse___rarg(x_675);
lean::inc(x_1);
x_678 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_677, x_642);
if (lean::obj_tag(x_678) == 0)
{
obj* x_679; obj* x_680; obj* x_681; obj* x_682; obj* x_683; obj* x_684; 
x_679 = lean::cnstr_get(x_678, 1);
lean::inc(x_679);
if (lean::is_exclusive(x_678)) {
 lean::cnstr_release(x_678, 0);
 lean::cnstr_release(x_678, 1);
 x_680 = x_678;
} else {
 lean::dec_ref(x_678);
 x_680 = lean::box(0);
}
if (lean::is_scalar(x_680)) {
 x_681 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_681 = x_680;
}
lean::cnstr_set(x_681, 0, x_641);
lean::cnstr_set(x_681, 1, x_679);
lean::inc(x_626);
lean::inc(x_672);
x_682 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_682, 0, x_672);
lean::closure_set(x_682, 1, x_626);
x_683 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_684 = l_Lean_profileitPure___rarg(x_683, x_634, x_682, x_681);
if (lean::obj_tag(x_684) == 0)
{
obj* x_685; obj* x_686; obj* x_687; obj* x_688; 
x_685 = lean::cnstr_get(x_684, 0);
lean::inc(x_685);
x_686 = lean::cnstr_get(x_684, 1);
lean::inc(x_686);
if (lean::is_exclusive(x_684)) {
 lean::cnstr_release(x_684, 0);
 lean::cnstr_release(x_684, 1);
 x_687 = x_684;
} else {
 lean::dec_ref(x_684);
 x_687 = lean::box(0);
}
if (lean::is_scalar(x_687)) {
 x_688 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_688 = x_687;
}
lean::cnstr_set(x_688, 0, x_641);
lean::cnstr_set(x_688, 1, x_686);
if (lean::obj_tag(x_685) == 0)
{
lean::dec(x_634);
if (x_2 == 0)
{
obj* x_689; obj* x_690; obj* x_691; obj* x_692; obj* x_693; obj* x_694; 
lean::dec(x_672);
lean::dec(x_627);
x_689 = lean::cnstr_get(x_685, 0);
lean::inc(x_689);
lean::dec(x_685);
lean::inc(x_5);
if (lean::is_scalar(x_676)) {
 x_690 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_690 = x_676;
}
lean::cnstr_set(x_690, 0, x_626);
lean::cnstr_set(x_690, 1, x_5);
if (lean::is_scalar(x_673)) {
 x_691 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_691 = x_673;
}
lean::cnstr_set(x_691, 0, x_23);
lean::cnstr_set(x_691, 1, x_690);
x_692 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_692, 0, x_21);
lean::cnstr_set(x_692, 1, x_691);
lean::cnstr_set(x_18, 1, x_692);
lean::cnstr_set(x_18, 0, x_674);
x_693 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_693, 0, x_18);
lean::inc(x_1);
x_694 = lean::apply_2(x_1, x_689, x_688);
if (lean::obj_tag(x_694) == 0)
{
obj* x_695; 
x_695 = lean::cnstr_get(x_694, 1);
lean::inc(x_695);
lean::dec(x_694);
x_8 = x_693;
x_9 = x_695;
goto block_16;
}
else
{
obj* x_696; obj* x_697; obj* x_698; obj* x_699; 
lean::dec(x_693);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_696 = lean::cnstr_get(x_694, 0);
lean::inc(x_696);
x_697 = lean::cnstr_get(x_694, 1);
lean::inc(x_697);
if (lean::is_exclusive(x_694)) {
 lean::cnstr_release(x_694, 0);
 lean::cnstr_release(x_694, 1);
 x_698 = x_694;
} else {
 lean::dec_ref(x_694);
 x_698 = lean::box(0);
}
if (lean::is_scalar(x_698)) {
 x_699 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_699 = x_698;
}
lean::cnstr_set(x_699, 0, x_696);
lean::cnstr_set(x_699, 1, x_697);
return x_699;
}
}
else
{
obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_705; obj* x_706; 
x_700 = lean::cnstr_get(x_685, 0);
lean::inc(x_700);
lean::dec(x_685);
x_701 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_701, 0, x_672);
lean::cnstr_set(x_701, 1, x_627);
if (lean::is_scalar(x_676)) {
 x_702 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_702 = x_676;
}
lean::cnstr_set(x_702, 0, x_626);
lean::cnstr_set(x_702, 1, x_701);
if (lean::is_scalar(x_673)) {
 x_703 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_703 = x_673;
}
lean::cnstr_set(x_703, 0, x_23);
lean::cnstr_set(x_703, 1, x_702);
x_704 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_704, 0, x_21);
lean::cnstr_set(x_704, 1, x_703);
lean::cnstr_set(x_18, 1, x_704);
lean::cnstr_set(x_18, 0, x_674);
x_705 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_705, 0, x_18);
lean::inc(x_1);
x_706 = lean::apply_2(x_1, x_700, x_688);
if (lean::obj_tag(x_706) == 0)
{
obj* x_707; 
x_707 = lean::cnstr_get(x_706, 1);
lean::inc(x_707);
lean::dec(x_706);
x_8 = x_705;
x_9 = x_707;
goto block_16;
}
else
{
obj* x_708; obj* x_709; obj* x_710; obj* x_711; 
lean::dec(x_705);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_708 = lean::cnstr_get(x_706, 0);
lean::inc(x_708);
x_709 = lean::cnstr_get(x_706, 1);
lean::inc(x_709);
if (lean::is_exclusive(x_706)) {
 lean::cnstr_release(x_706, 0);
 lean::cnstr_release(x_706, 1);
 x_710 = x_706;
} else {
 lean::dec_ref(x_706);
 x_710 = lean::box(0);
}
if (lean::is_scalar(x_710)) {
 x_711 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_711 = x_710;
}
lean::cnstr_set(x_711, 0, x_708);
lean::cnstr_set(x_711, 1, x_709);
return x_711;
}
}
}
else
{
obj* x_712; obj* x_713; obj* x_714; obj* x_715; 
lean::dec(x_626);
lean::dec(x_23);
x_712 = lean::cnstr_get(x_685, 0);
lean::inc(x_712);
lean::dec(x_685);
lean::inc(x_712);
lean::inc(x_4);
x_713 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_713, 0, x_4);
lean::closure_set(x_713, 1, x_21);
lean::closure_set(x_713, 2, x_712);
x_714 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_715 = l_Lean_profileitPure___rarg(x_714, x_634, x_713, x_688);
lean::dec(x_634);
if (lean::obj_tag(x_715) == 0)
{
obj* x_716; obj* x_717; obj* x_718; obj* x_719; obj* x_720; obj* x_721; obj* x_722; 
x_716 = lean::cnstr_get(x_715, 0);
lean::inc(x_716);
x_717 = lean::cnstr_get(x_715, 1);
lean::inc(x_717);
if (lean::is_exclusive(x_715)) {
 lean::cnstr_release(x_715, 0);
 lean::cnstr_release(x_715, 1);
 x_718 = x_715;
} else {
 lean::dec_ref(x_715);
 x_718 = lean::box(0);
}
if (lean::is_scalar(x_718)) {
 x_719 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_719 = x_718;
}
lean::cnstr_set(x_719, 0, x_641);
lean::cnstr_set(x_719, 1, x_717);
x_720 = lean::cnstr_get(x_716, 5);
lean::inc(x_720);
x_721 = l_List_reverse___rarg(x_720);
lean::inc(x_1);
x_722 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_721, x_719);
if (lean::obj_tag(x_722) == 0)
{
obj* x_723; obj* x_724; uint8 x_725; 
x_723 = lean::cnstr_get(x_722, 1);
lean::inc(x_723);
lean::dec(x_722);
x_724 = l_Lean_Parser_Module_eoi;
x_725 = l_Lean_Parser_Syntax_isOfKind___main(x_724, x_712);
lean::dec(x_712);
if (x_725 == 0)
{
if (x_2 == 0)
{
obj* x_726; obj* x_727; obj* x_728; obj* x_729; obj* x_730; obj* x_731; 
lean::dec(x_672);
lean::dec(x_627);
x_726 = lean::cnstr_get(x_716, 6);
lean::inc(x_726);
x_727 = lean::cnstr_get(x_716, 7);
lean::inc(x_727);
lean::inc(x_5);
if (lean::is_scalar(x_676)) {
 x_728 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_728 = x_676;
}
lean::cnstr_set(x_728, 0, x_727);
lean::cnstr_set(x_728, 1, x_5);
if (lean::is_scalar(x_673)) {
 x_729 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_729 = x_673;
}
lean::cnstr_set(x_729, 0, x_726);
lean::cnstr_set(x_729, 1, x_728);
x_730 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_730, 0, x_716);
lean::cnstr_set(x_730, 1, x_729);
lean::cnstr_set(x_18, 1, x_730);
lean::cnstr_set(x_18, 0, x_674);
x_731 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_731, 0, x_18);
x_8 = x_731;
x_9 = x_723;
goto block_16;
}
else
{
obj* x_732; obj* x_733; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; 
x_732 = lean::cnstr_get(x_716, 6);
lean::inc(x_732);
x_733 = lean::cnstr_get(x_716, 7);
lean::inc(x_733);
x_734 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_734, 0, x_672);
lean::cnstr_set(x_734, 1, x_627);
if (lean::is_scalar(x_676)) {
 x_735 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_735 = x_676;
}
lean::cnstr_set(x_735, 0, x_733);
lean::cnstr_set(x_735, 1, x_734);
if (lean::is_scalar(x_673)) {
 x_736 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_736 = x_673;
}
lean::cnstr_set(x_736, 0, x_732);
lean::cnstr_set(x_736, 1, x_735);
x_737 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_737, 0, x_716);
lean::cnstr_set(x_737, 1, x_736);
lean::cnstr_set(x_18, 1, x_737);
lean::cnstr_set(x_18, 0, x_674);
x_738 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_738, 0, x_18);
x_8 = x_738;
x_9 = x_723;
goto block_16;
}
}
else
{
lean::dec(x_674);
lean::dec(x_673);
lean::free_heap_obj(x_18);
if (x_2 == 0)
{
obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
lean::dec(x_672);
lean::dec(x_627);
x_739 = lean::cnstr_get(x_716, 8);
lean::inc(x_739);
lean::dec(x_716);
lean::inc(x_5);
x_740 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_676)) {
 x_741 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_741 = x_676;
}
lean::cnstr_set(x_741, 0, x_740);
lean::cnstr_set(x_741, 1, x_739);
x_742 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_742, 0, x_741);
x_8 = x_742;
x_9 = x_723;
goto block_16;
}
else
{
obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; 
x_743 = lean::cnstr_get(x_716, 8);
lean::inc(x_743);
lean::dec(x_716);
x_744 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_744, 0, x_672);
lean::cnstr_set(x_744, 1, x_627);
x_745 = l_List_reverse___rarg(x_744);
if (lean::is_scalar(x_676)) {
 x_746 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_746 = x_676;
}
lean::cnstr_set(x_746, 0, x_745);
lean::cnstr_set(x_746, 1, x_743);
x_747 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_747, 0, x_746);
x_8 = x_747;
x_9 = x_723;
goto block_16;
}
}
}
else
{
obj* x_748; obj* x_749; obj* x_750; obj* x_751; 
lean::dec(x_716);
lean::dec(x_712);
lean::dec(x_676);
lean::dec(x_674);
lean::dec(x_673);
lean::dec(x_672);
lean::dec(x_627);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_748 = lean::cnstr_get(x_722, 0);
lean::inc(x_748);
x_749 = lean::cnstr_get(x_722, 1);
lean::inc(x_749);
if (lean::is_exclusive(x_722)) {
 lean::cnstr_release(x_722, 0);
 lean::cnstr_release(x_722, 1);
 x_750 = x_722;
} else {
 lean::dec_ref(x_722);
 x_750 = lean::box(0);
}
if (lean::is_scalar(x_750)) {
 x_751 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_751 = x_750;
}
lean::cnstr_set(x_751, 0, x_748);
lean::cnstr_set(x_751, 1, x_749);
return x_751;
}
}
else
{
obj* x_752; obj* x_753; obj* x_754; obj* x_755; 
lean::dec(x_712);
lean::dec(x_676);
lean::dec(x_674);
lean::dec(x_673);
lean::dec(x_672);
lean::dec(x_627);
lean::free_heap_obj(x_18);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_752 = lean::cnstr_get(x_715, 0);
lean::inc(x_752);
x_753 = lean::cnstr_get(x_715, 1);
lean::inc(x_753);
if (lean::is_exclusive(x_715)) {
 lean::cnstr_release(x_715, 0);
 lean::cnstr_release(x_715, 1);
 x_754 = x_715;
} else {
 lean::dec_ref(x_715);
 x_754 = lean::box(0);
}
if (lean::is_scalar(x_754)) {
 x_755 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_755 = x_754;
}
lean::cnstr_set(x_755, 0, x_752);
lean::cnstr_set(x_755, 1, x_753);
return x_755;
}
}
}
else
{
obj* x_756; obj* x_757; obj* x_758; obj* x_759; 
lean::dec(x_676);
lean::dec(x_674);
lean::dec(x_673);
lean::dec(x_672);
lean::dec(x_634);
lean::dec(x_627);
lean::dec(x_626);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_756 = lean::cnstr_get(x_684, 0);
lean::inc(x_756);
x_757 = lean::cnstr_get(x_684, 1);
lean::inc(x_757);
if (lean::is_exclusive(x_684)) {
 lean::cnstr_release(x_684, 0);
 lean::cnstr_release(x_684, 1);
 x_758 = x_684;
} else {
 lean::dec_ref(x_684);
 x_758 = lean::box(0);
}
if (lean::is_scalar(x_758)) {
 x_759 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_759 = x_758;
}
lean::cnstr_set(x_759, 0, x_756);
lean::cnstr_set(x_759, 1, x_757);
return x_759;
}
}
else
{
obj* x_760; obj* x_761; obj* x_762; obj* x_763; 
lean::dec(x_676);
lean::dec(x_674);
lean::dec(x_673);
lean::dec(x_672);
lean::dec(x_634);
lean::dec(x_627);
lean::dec(x_626);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_760 = lean::cnstr_get(x_678, 0);
lean::inc(x_760);
x_761 = lean::cnstr_get(x_678, 1);
lean::inc(x_761);
if (lean::is_exclusive(x_678)) {
 lean::cnstr_release(x_678, 0);
 lean::cnstr_release(x_678, 1);
 x_762 = x_678;
} else {
 lean::dec_ref(x_678);
 x_762 = lean::box(0);
}
if (lean::is_scalar(x_762)) {
 x_763 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_763 = x_762;
}
lean::cnstr_set(x_763, 0, x_760);
lean::cnstr_set(x_763, 1, x_761);
return x_763;
}
}
}
else
{
obj* x_764; obj* x_765; obj* x_766; obj* x_767; 
lean::dec(x_634);
lean::dec(x_627);
lean::dec(x_626);
lean::free_heap_obj(x_18);
lean::dec(x_23);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_764 = lean::cnstr_get(x_637, 0);
lean::inc(x_764);
x_765 = lean::cnstr_get(x_637, 1);
lean::inc(x_765);
if (lean::is_exclusive(x_637)) {
 lean::cnstr_release(x_637, 0);
 lean::cnstr_release(x_637, 1);
 x_766 = x_637;
} else {
 lean::dec_ref(x_637);
 x_766 = lean::box(0);
}
if (lean::is_scalar(x_766)) {
 x_767 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_767 = x_766;
}
lean::cnstr_set(x_767, 0, x_764);
lean::cnstr_set(x_767, 1, x_765);
return x_767;
}
}
}
else
{
obj* x_768; obj* x_769; obj* x_770; obj* x_771; obj* x_772; obj* x_773; obj* x_774; obj* x_775; obj* x_776; obj* x_777; obj* x_778; obj* x_779; obj* x_780; obj* x_781; 
x_768 = lean::cnstr_get(x_18, 0);
lean::inc(x_768);
lean::dec(x_18);
x_769 = lean::cnstr_get(x_19, 0);
lean::inc(x_769);
x_770 = lean::cnstr_get(x_19, 1);
lean::inc(x_770);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_771 = x_19;
} else {
 lean::dec_ref(x_19);
 x_771 = lean::box(0);
}
x_772 = lean::cnstr_get(x_768, 0);
lean::inc(x_772);
x_773 = lean::cnstr_get(x_772, 0);
lean::inc(x_773);
lean::dec(x_772);
x_774 = lean::cnstr_get(x_773, 0);
lean::inc(x_774);
lean::dec(x_773);
x_775 = lean::cnstr_get(x_774, 2);
lean::inc(x_775);
lean::dec(x_774);
x_776 = lean::cnstr_get(x_20, 0);
lean::inc(x_776);
x_777 = lean::cnstr_get(x_776, 1);
lean::inc(x_777);
lean::dec(x_776);
x_778 = l_Lean_FileMap_toPosition(x_775, x_777);
lean::dec(x_775);
lean::inc(x_768);
x_779 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_779, 0, x_768);
lean::closure_set(x_779, 1, x_20);
x_780 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__1;
x_781 = l_Lean_profileitPure___rarg(x_780, x_778, x_779, x_7);
if (lean::obj_tag(x_781) == 0)
{
obj* x_782; obj* x_783; obj* x_784; obj* x_785; obj* x_786; obj* x_787; 
x_782 = lean::cnstr_get(x_781, 0);
lean::inc(x_782);
x_783 = lean::cnstr_get(x_781, 1);
lean::inc(x_783);
if (lean::is_exclusive(x_781)) {
 lean::cnstr_release(x_781, 0);
 lean::cnstr_release(x_781, 1);
 x_784 = x_781;
} else {
 lean::dec_ref(x_781);
 x_784 = lean::box(0);
}
x_785 = lean::box(0);
if (lean::is_scalar(x_784)) {
 x_786 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_786 = x_784;
}
lean::cnstr_set(x_786, 0, x_785);
lean::cnstr_set(x_786, 1, x_783);
x_787 = lean::cnstr_get(x_782, 1);
lean::inc(x_787);
if (lean::obj_tag(x_787) == 0)
{
obj* x_788; obj* x_789; obj* x_790; obj* x_791; 
lean::dec(x_778);
lean::dec(x_771);
lean::dec(x_769);
lean::dec(x_768);
x_788 = lean::cnstr_get(x_782, 0);
lean::inc(x_788);
if (lean::is_exclusive(x_782)) {
 lean::cnstr_release(x_782, 0);
 lean::cnstr_release(x_782, 1);
 x_789 = x_782;
} else {
 lean::dec_ref(x_782);
 x_789 = lean::box(0);
}
x_790 = lean::cnstr_get(x_787, 0);
lean::inc(x_790);
lean::dec(x_787);
lean::inc(x_1);
x_791 = lean::apply_2(x_1, x_790, x_786);
if (lean::obj_tag(x_791) == 0)
{
obj* x_792; obj* x_793; obj* x_794; obj* x_795; 
x_792 = lean::cnstr_get(x_791, 1);
lean::inc(x_792);
if (lean::is_exclusive(x_791)) {
 lean::cnstr_release(x_791, 0);
 lean::cnstr_release(x_791, 1);
 x_793 = x_791;
} else {
 lean::dec_ref(x_791);
 x_793 = lean::box(0);
}
if (lean::is_scalar(x_793)) {
 x_794 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_794 = x_793;
}
lean::cnstr_set(x_794, 0, x_785);
lean::cnstr_set(x_794, 1, x_792);
lean::inc(x_3);
lean::inc(x_1);
x_795 = l_List_mfor___main___at_Lean_runFrontend___spec__3(x_1, x_3, x_794);
if (lean::obj_tag(x_795) == 0)
{
if (x_2 == 0)
{
obj* x_796; obj* x_797; obj* x_798; obj* x_799; obj* x_800; 
lean::dec(x_788);
lean::dec(x_770);
x_796 = lean::cnstr_get(x_795, 1);
lean::inc(x_796);
lean::dec(x_795);
x_797 = lean::cnstr_get(x_21, 8);
lean::inc(x_797);
lean::dec(x_21);
lean::inc(x_5);
x_798 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_789)) {
 x_799 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_799 = x_789;
}
lean::cnstr_set(x_799, 0, x_798);
lean::cnstr_set(x_799, 1, x_797);
x_800 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_800, 0, x_799);
x_8 = x_800;
x_9 = x_796;
goto block_16;
}
else
{
obj* x_801; obj* x_802; obj* x_803; obj* x_804; obj* x_805; obj* x_806; 
x_801 = lean::cnstr_get(x_795, 1);
lean::inc(x_801);
lean::dec(x_795);
x_802 = lean::cnstr_get(x_21, 8);
lean::inc(x_802);
lean::dec(x_21);
x_803 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_803, 0, x_788);
lean::cnstr_set(x_803, 1, x_770);
x_804 = l_List_reverse___rarg(x_803);
if (lean::is_scalar(x_789)) {
 x_805 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_805 = x_789;
}
lean::cnstr_set(x_805, 0, x_804);
lean::cnstr_set(x_805, 1, x_802);
x_806 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_806, 0, x_805);
x_8 = x_806;
x_9 = x_801;
goto block_16;
}
}
else
{
obj* x_807; obj* x_808; obj* x_809; obj* x_810; 
lean::dec(x_789);
lean::dec(x_788);
lean::dec(x_770);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_807 = lean::cnstr_get(x_795, 0);
lean::inc(x_807);
x_808 = lean::cnstr_get(x_795, 1);
lean::inc(x_808);
if (lean::is_exclusive(x_795)) {
 lean::cnstr_release(x_795, 0);
 lean::cnstr_release(x_795, 1);
 x_809 = x_795;
} else {
 lean::dec_ref(x_795);
 x_809 = lean::box(0);
}
if (lean::is_scalar(x_809)) {
 x_810 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_810 = x_809;
}
lean::cnstr_set(x_810, 0, x_807);
lean::cnstr_set(x_810, 1, x_808);
return x_810;
}
}
else
{
obj* x_811; obj* x_812; obj* x_813; obj* x_814; 
lean::dec(x_789);
lean::dec(x_788);
lean::dec(x_770);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_811 = lean::cnstr_get(x_791, 0);
lean::inc(x_811);
x_812 = lean::cnstr_get(x_791, 1);
lean::inc(x_812);
if (lean::is_exclusive(x_791)) {
 lean::cnstr_release(x_791, 0);
 lean::cnstr_release(x_791, 1);
 x_813 = x_791;
} else {
 lean::dec_ref(x_791);
 x_813 = lean::box(0);
}
if (lean::is_scalar(x_813)) {
 x_814 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_814 = x_813;
}
lean::cnstr_set(x_814, 0, x_811);
lean::cnstr_set(x_814, 1, x_812);
return x_814;
}
}
else
{
obj* x_815; obj* x_816; obj* x_817; obj* x_818; obj* x_819; obj* x_820; obj* x_821; obj* x_822; 
x_815 = lean::cnstr_get(x_787, 0);
lean::inc(x_815);
lean::dec(x_787);
x_816 = lean::cnstr_get(x_782, 0);
lean::inc(x_816);
if (lean::is_exclusive(x_782)) {
 lean::cnstr_release(x_782, 0);
 lean::cnstr_release(x_782, 1);
 x_817 = x_782;
} else {
 lean::dec_ref(x_782);
 x_817 = lean::box(0);
}
x_818 = lean::cnstr_get(x_815, 0);
lean::inc(x_818);
x_819 = lean::cnstr_get(x_815, 1);
lean::inc(x_819);
if (lean::is_exclusive(x_815)) {
 lean::cnstr_release(x_815, 0);
 lean::cnstr_release(x_815, 1);
 x_820 = x_815;
} else {
 lean::dec_ref(x_815);
 x_820 = lean::box(0);
}
x_821 = l_List_reverse___rarg(x_819);
lean::inc(x_1);
x_822 = l_List_mfor___main___at_Lean_runFrontend___spec__4(x_1, x_821, x_786);
if (lean::obj_tag(x_822) == 0)
{
obj* x_823; obj* x_824; obj* x_825; obj* x_826; obj* x_827; obj* x_828; 
x_823 = lean::cnstr_get(x_822, 1);
lean::inc(x_823);
if (lean::is_exclusive(x_822)) {
 lean::cnstr_release(x_822, 0);
 lean::cnstr_release(x_822, 1);
 x_824 = x_822;
} else {
 lean::dec_ref(x_822);
 x_824 = lean::box(0);
}
if (lean::is_scalar(x_824)) {
 x_825 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_825 = x_824;
}
lean::cnstr_set(x_825, 0, x_785);
lean::cnstr_set(x_825, 1, x_823);
lean::inc(x_769);
lean::inc(x_816);
x_826 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_826, 0, x_816);
lean::closure_set(x_826, 1, x_769);
x_827 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__2;
x_828 = l_Lean_profileitPure___rarg(x_827, x_778, x_826, x_825);
if (lean::obj_tag(x_828) == 0)
{
obj* x_829; obj* x_830; obj* x_831; obj* x_832; 
x_829 = lean::cnstr_get(x_828, 0);
lean::inc(x_829);
x_830 = lean::cnstr_get(x_828, 1);
lean::inc(x_830);
if (lean::is_exclusive(x_828)) {
 lean::cnstr_release(x_828, 0);
 lean::cnstr_release(x_828, 1);
 x_831 = x_828;
} else {
 lean::dec_ref(x_828);
 x_831 = lean::box(0);
}
if (lean::is_scalar(x_831)) {
 x_832 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_832 = x_831;
}
lean::cnstr_set(x_832, 0, x_785);
lean::cnstr_set(x_832, 1, x_830);
if (lean::obj_tag(x_829) == 0)
{
lean::dec(x_778);
if (x_2 == 0)
{
obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_838; obj* x_839; 
lean::dec(x_816);
lean::dec(x_770);
x_833 = lean::cnstr_get(x_829, 0);
lean::inc(x_833);
lean::dec(x_829);
lean::inc(x_5);
if (lean::is_scalar(x_820)) {
 x_834 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_834 = x_820;
}
lean::cnstr_set(x_834, 0, x_769);
lean::cnstr_set(x_834, 1, x_5);
if (lean::is_scalar(x_817)) {
 x_835 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_835 = x_817;
}
lean::cnstr_set(x_835, 0, x_768);
lean::cnstr_set(x_835, 1, x_834);
if (lean::is_scalar(x_771)) {
 x_836 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_836 = x_771;
}
lean::cnstr_set(x_836, 0, x_21);
lean::cnstr_set(x_836, 1, x_835);
x_837 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_837, 0, x_818);
lean::cnstr_set(x_837, 1, x_836);
x_838 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_838, 0, x_837);
lean::inc(x_1);
x_839 = lean::apply_2(x_1, x_833, x_832);
if (lean::obj_tag(x_839) == 0)
{
obj* x_840; 
x_840 = lean::cnstr_get(x_839, 1);
lean::inc(x_840);
lean::dec(x_839);
x_8 = x_838;
x_9 = x_840;
goto block_16;
}
else
{
obj* x_841; obj* x_842; obj* x_843; obj* x_844; 
lean::dec(x_838);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_841 = lean::cnstr_get(x_839, 0);
lean::inc(x_841);
x_842 = lean::cnstr_get(x_839, 1);
lean::inc(x_842);
if (lean::is_exclusive(x_839)) {
 lean::cnstr_release(x_839, 0);
 lean::cnstr_release(x_839, 1);
 x_843 = x_839;
} else {
 lean::dec_ref(x_839);
 x_843 = lean::box(0);
}
if (lean::is_scalar(x_843)) {
 x_844 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_844 = x_843;
}
lean::cnstr_set(x_844, 0, x_841);
lean::cnstr_set(x_844, 1, x_842);
return x_844;
}
}
else
{
obj* x_845; obj* x_846; obj* x_847; obj* x_848; obj* x_849; obj* x_850; obj* x_851; obj* x_852; 
x_845 = lean::cnstr_get(x_829, 0);
lean::inc(x_845);
lean::dec(x_829);
x_846 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_846, 0, x_816);
lean::cnstr_set(x_846, 1, x_770);
if (lean::is_scalar(x_820)) {
 x_847 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_847 = x_820;
}
lean::cnstr_set(x_847, 0, x_769);
lean::cnstr_set(x_847, 1, x_846);
if (lean::is_scalar(x_817)) {
 x_848 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_848 = x_817;
}
lean::cnstr_set(x_848, 0, x_768);
lean::cnstr_set(x_848, 1, x_847);
if (lean::is_scalar(x_771)) {
 x_849 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_849 = x_771;
}
lean::cnstr_set(x_849, 0, x_21);
lean::cnstr_set(x_849, 1, x_848);
x_850 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_850, 0, x_818);
lean::cnstr_set(x_850, 1, x_849);
x_851 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_851, 0, x_850);
lean::inc(x_1);
x_852 = lean::apply_2(x_1, x_845, x_832);
if (lean::obj_tag(x_852) == 0)
{
obj* x_853; 
x_853 = lean::cnstr_get(x_852, 1);
lean::inc(x_853);
lean::dec(x_852);
x_8 = x_851;
x_9 = x_853;
goto block_16;
}
else
{
obj* x_854; obj* x_855; obj* x_856; obj* x_857; 
lean::dec(x_851);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_854 = lean::cnstr_get(x_852, 0);
lean::inc(x_854);
x_855 = lean::cnstr_get(x_852, 1);
lean::inc(x_855);
if (lean::is_exclusive(x_852)) {
 lean::cnstr_release(x_852, 0);
 lean::cnstr_release(x_852, 1);
 x_856 = x_852;
} else {
 lean::dec_ref(x_852);
 x_856 = lean::box(0);
}
if (lean::is_scalar(x_856)) {
 x_857 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_857 = x_856;
}
lean::cnstr_set(x_857, 0, x_854);
lean::cnstr_set(x_857, 1, x_855);
return x_857;
}
}
}
else
{
obj* x_858; obj* x_859; obj* x_860; obj* x_861; 
lean::dec(x_769);
lean::dec(x_768);
x_858 = lean::cnstr_get(x_829, 0);
lean::inc(x_858);
lean::dec(x_829);
lean::inc(x_858);
lean::inc(x_4);
x_859 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_859, 0, x_4);
lean::closure_set(x_859, 1, x_21);
lean::closure_set(x_859, 2, x_858);
x_860 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___closed__3;
x_861 = l_Lean_profileitPure___rarg(x_860, x_778, x_859, x_832);
lean::dec(x_778);
if (lean::obj_tag(x_861) == 0)
{
obj* x_862; obj* x_863; obj* x_864; obj* x_865; obj* x_866; obj* x_867; obj* x_868; 
x_862 = lean::cnstr_get(x_861, 0);
lean::inc(x_862);
x_863 = lean::cnstr_get(x_861, 1);
lean::inc(x_863);
if (lean::is_exclusive(x_861)) {
 lean::cnstr_release(x_861, 0);
 lean::cnstr_release(x_861, 1);
 x_864 = x_861;
} else {
 lean::dec_ref(x_861);
 x_864 = lean::box(0);
}
if (lean::is_scalar(x_864)) {
 x_865 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_865 = x_864;
}
lean::cnstr_set(x_865, 0, x_785);
lean::cnstr_set(x_865, 1, x_863);
x_866 = lean::cnstr_get(x_862, 5);
lean::inc(x_866);
x_867 = l_List_reverse___rarg(x_866);
lean::inc(x_1);
x_868 = l_List_mfor___main___at_Lean_runFrontend___spec__5(x_1, x_867, x_865);
if (lean::obj_tag(x_868) == 0)
{
obj* x_869; obj* x_870; uint8 x_871; 
x_869 = lean::cnstr_get(x_868, 1);
lean::inc(x_869);
lean::dec(x_868);
x_870 = l_Lean_Parser_Module_eoi;
x_871 = l_Lean_Parser_Syntax_isOfKind___main(x_870, x_858);
lean::dec(x_858);
if (x_871 == 0)
{
if (x_2 == 0)
{
obj* x_872; obj* x_873; obj* x_874; obj* x_875; obj* x_876; obj* x_877; obj* x_878; 
lean::dec(x_816);
lean::dec(x_770);
x_872 = lean::cnstr_get(x_862, 6);
lean::inc(x_872);
x_873 = lean::cnstr_get(x_862, 7);
lean::inc(x_873);
lean::inc(x_5);
if (lean::is_scalar(x_820)) {
 x_874 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_874 = x_820;
}
lean::cnstr_set(x_874, 0, x_873);
lean::cnstr_set(x_874, 1, x_5);
if (lean::is_scalar(x_817)) {
 x_875 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_875 = x_817;
}
lean::cnstr_set(x_875, 0, x_872);
lean::cnstr_set(x_875, 1, x_874);
if (lean::is_scalar(x_771)) {
 x_876 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_876 = x_771;
}
lean::cnstr_set(x_876, 0, x_862);
lean::cnstr_set(x_876, 1, x_875);
x_877 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_877, 0, x_818);
lean::cnstr_set(x_877, 1, x_876);
x_878 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_878, 0, x_877);
x_8 = x_878;
x_9 = x_869;
goto block_16;
}
else
{
obj* x_879; obj* x_880; obj* x_881; obj* x_882; obj* x_883; obj* x_884; obj* x_885; obj* x_886; 
x_879 = lean::cnstr_get(x_862, 6);
lean::inc(x_879);
x_880 = lean::cnstr_get(x_862, 7);
lean::inc(x_880);
x_881 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_881, 0, x_816);
lean::cnstr_set(x_881, 1, x_770);
if (lean::is_scalar(x_820)) {
 x_882 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_882 = x_820;
}
lean::cnstr_set(x_882, 0, x_880);
lean::cnstr_set(x_882, 1, x_881);
if (lean::is_scalar(x_817)) {
 x_883 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_883 = x_817;
}
lean::cnstr_set(x_883, 0, x_879);
lean::cnstr_set(x_883, 1, x_882);
if (lean::is_scalar(x_771)) {
 x_884 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_884 = x_771;
}
lean::cnstr_set(x_884, 0, x_862);
lean::cnstr_set(x_884, 1, x_883);
x_885 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_885, 0, x_818);
lean::cnstr_set(x_885, 1, x_884);
x_886 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_886, 0, x_885);
x_8 = x_886;
x_9 = x_869;
goto block_16;
}
}
else
{
lean::dec(x_818);
lean::dec(x_817);
lean::dec(x_771);
if (x_2 == 0)
{
obj* x_887; obj* x_888; obj* x_889; obj* x_890; 
lean::dec(x_816);
lean::dec(x_770);
x_887 = lean::cnstr_get(x_862, 8);
lean::inc(x_887);
lean::dec(x_862);
lean::inc(x_5);
x_888 = l_List_reverse___rarg(x_5);
if (lean::is_scalar(x_820)) {
 x_889 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_889 = x_820;
}
lean::cnstr_set(x_889, 0, x_888);
lean::cnstr_set(x_889, 1, x_887);
x_890 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_890, 0, x_889);
x_8 = x_890;
x_9 = x_869;
goto block_16;
}
else
{
obj* x_891; obj* x_892; obj* x_893; obj* x_894; obj* x_895; 
x_891 = lean::cnstr_get(x_862, 8);
lean::inc(x_891);
lean::dec(x_862);
x_892 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_892, 0, x_816);
lean::cnstr_set(x_892, 1, x_770);
x_893 = l_List_reverse___rarg(x_892);
if (lean::is_scalar(x_820)) {
 x_894 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_894 = x_820;
}
lean::cnstr_set(x_894, 0, x_893);
lean::cnstr_set(x_894, 1, x_891);
x_895 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_895, 0, x_894);
x_8 = x_895;
x_9 = x_869;
goto block_16;
}
}
}
else
{
obj* x_896; obj* x_897; obj* x_898; obj* x_899; 
lean::dec(x_862);
lean::dec(x_858);
lean::dec(x_820);
lean::dec(x_818);
lean::dec(x_817);
lean::dec(x_816);
lean::dec(x_771);
lean::dec(x_770);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_896 = lean::cnstr_get(x_868, 0);
lean::inc(x_896);
x_897 = lean::cnstr_get(x_868, 1);
lean::inc(x_897);
if (lean::is_exclusive(x_868)) {
 lean::cnstr_release(x_868, 0);
 lean::cnstr_release(x_868, 1);
 x_898 = x_868;
} else {
 lean::dec_ref(x_868);
 x_898 = lean::box(0);
}
if (lean::is_scalar(x_898)) {
 x_899 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_899 = x_898;
}
lean::cnstr_set(x_899, 0, x_896);
lean::cnstr_set(x_899, 1, x_897);
return x_899;
}
}
else
{
obj* x_900; obj* x_901; obj* x_902; obj* x_903; 
lean::dec(x_858);
lean::dec(x_820);
lean::dec(x_818);
lean::dec(x_817);
lean::dec(x_816);
lean::dec(x_771);
lean::dec(x_770);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_900 = lean::cnstr_get(x_861, 0);
lean::inc(x_900);
x_901 = lean::cnstr_get(x_861, 1);
lean::inc(x_901);
if (lean::is_exclusive(x_861)) {
 lean::cnstr_release(x_861, 0);
 lean::cnstr_release(x_861, 1);
 x_902 = x_861;
} else {
 lean::dec_ref(x_861);
 x_902 = lean::box(0);
}
if (lean::is_scalar(x_902)) {
 x_903 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_903 = x_902;
}
lean::cnstr_set(x_903, 0, x_900);
lean::cnstr_set(x_903, 1, x_901);
return x_903;
}
}
}
else
{
obj* x_904; obj* x_905; obj* x_906; obj* x_907; 
lean::dec(x_820);
lean::dec(x_818);
lean::dec(x_817);
lean::dec(x_816);
lean::dec(x_778);
lean::dec(x_771);
lean::dec(x_770);
lean::dec(x_769);
lean::dec(x_768);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_904 = lean::cnstr_get(x_828, 0);
lean::inc(x_904);
x_905 = lean::cnstr_get(x_828, 1);
lean::inc(x_905);
if (lean::is_exclusive(x_828)) {
 lean::cnstr_release(x_828, 0);
 lean::cnstr_release(x_828, 1);
 x_906 = x_828;
} else {
 lean::dec_ref(x_828);
 x_906 = lean::box(0);
}
if (lean::is_scalar(x_906)) {
 x_907 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_907 = x_906;
}
lean::cnstr_set(x_907, 0, x_904);
lean::cnstr_set(x_907, 1, x_905);
return x_907;
}
}
else
{
obj* x_908; obj* x_909; obj* x_910; obj* x_911; 
lean::dec(x_820);
lean::dec(x_818);
lean::dec(x_817);
lean::dec(x_816);
lean::dec(x_778);
lean::dec(x_771);
lean::dec(x_770);
lean::dec(x_769);
lean::dec(x_768);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_908 = lean::cnstr_get(x_822, 0);
lean::inc(x_908);
x_909 = lean::cnstr_get(x_822, 1);
lean::inc(x_909);
if (lean::is_exclusive(x_822)) {
 lean::cnstr_release(x_822, 0);
 lean::cnstr_release(x_822, 1);
 x_910 = x_822;
} else {
 lean::dec_ref(x_822);
 x_910 = lean::box(0);
}
if (lean::is_scalar(x_910)) {
 x_911 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_911 = x_910;
}
lean::cnstr_set(x_911, 0, x_908);
lean::cnstr_set(x_911, 1, x_909);
return x_911;
}
}
}
else
{
obj* x_912; obj* x_913; obj* x_914; obj* x_915; 
lean::dec(x_778);
lean::dec(x_771);
lean::dec(x_770);
lean::dec(x_769);
lean::dec(x_768);
lean::dec(x_21);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_912 = lean::cnstr_get(x_781, 0);
lean::inc(x_912);
x_913 = lean::cnstr_get(x_781, 1);
lean::inc(x_913);
if (lean::is_exclusive(x_781)) {
 lean::cnstr_release(x_781, 0);
 lean::cnstr_release(x_781, 1);
 x_914 = x_781;
} else {
 lean::dec_ref(x_781);
 x_914 = lean::box(0);
}
if (lean::is_scalar(x_914)) {
 x_915 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_915 = x_914;
}
lean::cnstr_set(x_915, 0, x_912);
lean::cnstr_set(x_915, 1, x_913);
return x_915;
}
}
block_16:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
x_6 = x_10;
x_7 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_9);
return x_15;
}
}
}
}
obj* _init_l_Lean_runFrontend___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::mk_string("trace");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("as_messages");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_Options_empty;
x_7 = 1;
x_8 = l_Lean_KVMap_setBool(x_6, x_5, x_7);
return x_8;
}
}
obj* l_Lean_runFrontend(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_Lean_mkConfig(x_1, x_2);
x_8 = l_ioOfExcept___at_Lean_runFrontend___spec__1(x_7, x_6);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::box(0);
lean::cnstr_set(x_8, 0, x_11);
lean::inc(x_10);
x_12 = l_Lean_Parser_parseHeader(x_10);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 1);
x_15 = lean::cnstr_get(x_12, 0);
lean::dec(x_15);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::box(0);
lean::cnstr_set(x_12, 1, x_5);
lean::cnstr_set(x_12, 0, x_17);
x_18 = lean::apply_2(x_3, x_16, x_8);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; 
x_20 = lean::cnstr_get(x_18, 0);
lean::dec(x_20);
lean::cnstr_set(x_18, 0, x_12);
return x_18;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8 x_23; 
lean::dec(x_12);
x_23 = !lean::is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_18, 0);
x_25 = lean::cnstr_get(x_18, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_18);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
obj* x_27; uint8 x_28; 
x_27 = lean::cnstr_get(x_14, 0);
lean::inc(x_27);
lean::dec(x_14);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
x_31 = l_List_reverse___rarg(x_30);
lean::inc(x_31);
lean::inc(x_3);
x_32 = l_List_mfor___main___at_Lean_runFrontend___spec__2(x_3, x_31, x_8);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint8 x_40; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_11);
x_35 = lean::cnstr_get(x_10, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_38 = l_Lean_Expander_builtinTransformers;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
x_40 = !lean::is_exclusive(x_37);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_41 = lean::cnstr_get(x_37, 1);
lean::dec(x_41);
x_42 = lean::cnstr_get(x_37, 0);
lean::dec(x_42);
lean::cnstr_set(x_37, 1, x_2);
lean::cnstr_set(x_37, 0, x_1);
lean::inc(x_10);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_37);
lean::cnstr_set(x_43, 1, x_10);
x_44 = l_Lean_runFrontend___closed__1;
x_45 = l_Lean_Elaborator_mkState(x_43, x_5, x_44);
x_46 = lean::box(0);
lean::cnstr_set(x_27, 1, x_46);
lean::cnstr_set(x_27, 0, x_39);
lean::cnstr_set(x_12, 1, x_27);
lean::cnstr_set(x_12, 0, x_10);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_12);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_29);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_31, x_43, x_46, x_48, x_32);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_50 = lean::cnstr_get(x_37, 2);
lean::inc(x_50);
lean::dec(x_37);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_1);
lean::cnstr_set(x_51, 1, x_2);
lean::cnstr_set(x_51, 2, x_50);
lean::inc(x_10);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_10);
x_53 = l_Lean_runFrontend___closed__1;
x_54 = l_Lean_Elaborator_mkState(x_52, x_5, x_53);
x_55 = lean::box(0);
lean::cnstr_set(x_27, 1, x_55);
lean::cnstr_set(x_27, 0, x_39);
lean::cnstr_set(x_12, 1, x_27);
lean::cnstr_set(x_12, 0, x_10);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_12);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_29);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_31, x_52, x_55, x_57, x_32);
return x_58;
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_59 = lean::cnstr_get(x_32, 1);
lean::inc(x_59);
lean::dec(x_32);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_11);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::cnstr_get(x_10, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
lean::dec(x_61);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
lean::dec(x_62);
x_64 = l_Lean_Expander_builtinTransformers;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::cnstr_get(x_63, 2);
lean::inc(x_66);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 lean::cnstr_release(x_63, 2);
 x_67 = x_63;
} else {
 lean::dec_ref(x_63);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_2);
lean::cnstr_set(x_68, 2, x_66);
lean::inc(x_10);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_10);
x_70 = l_Lean_runFrontend___closed__1;
x_71 = l_Lean_Elaborator_mkState(x_69, x_5, x_70);
x_72 = lean::box(0);
lean::cnstr_set(x_27, 1, x_72);
lean::cnstr_set(x_27, 0, x_65);
lean::cnstr_set(x_12, 1, x_27);
lean::cnstr_set(x_12, 0, x_10);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_12);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_29);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_31, x_69, x_72, x_74, x_60);
return x_75;
}
}
else
{
uint8 x_76; 
lean::dec(x_31);
lean::free_heap_obj(x_27);
lean::dec(x_29);
lean::free_heap_obj(x_12);
lean::dec(x_10);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_76 = !lean::is_exclusive(x_32);
if (x_76 == 0)
{
return x_32;
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_32, 0);
x_78 = lean::cnstr_get(x_32, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_32);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_80 = lean::cnstr_get(x_27, 0);
x_81 = lean::cnstr_get(x_27, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_27);
x_82 = l_List_reverse___rarg(x_81);
lean::inc(x_82);
lean::inc(x_3);
x_83 = l_List_mfor___main___at_Lean_runFrontend___spec__2(x_3, x_82, x_8);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_85 = x_83;
} else {
 lean::dec_ref(x_83);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_11);
lean::cnstr_set(x_86, 1, x_84);
x_87 = lean::cnstr_get(x_10, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
lean::dec(x_87);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
lean::dec(x_88);
x_90 = l_Lean_Expander_builtinTransformers;
lean::inc(x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 lean::cnstr_release(x_89, 2);
 x_93 = x_89;
} else {
 lean::dec_ref(x_89);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_1);
lean::cnstr_set(x_94, 1, x_2);
lean::cnstr_set(x_94, 2, x_92);
lean::inc(x_10);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_10);
x_96 = l_Lean_runFrontend___closed__1;
x_97 = l_Lean_Elaborator_mkState(x_95, x_5, x_96);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_91);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set(x_12, 1, x_99);
lean::cnstr_set(x_12, 0, x_10);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_97);
lean::cnstr_set(x_100, 1, x_12);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_80);
lean::cnstr_set(x_101, 1, x_100);
x_102 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_82, x_95, x_98, x_101, x_86);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_82);
lean::dec(x_80);
lean::free_heap_obj(x_12);
lean::dec(x_10);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_103 = lean::cnstr_get(x_83, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_83, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_105 = x_83;
} else {
 lean::dec_ref(x_83);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_104);
return x_106;
}
}
}
}
else
{
obj* x_107; 
x_107 = lean::cnstr_get(x_12, 1);
lean::inc(x_107);
lean::dec(x_12);
if (lean::obj_tag(x_107) == 0)
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_1);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
lean::dec(x_107);
x_109 = lean::box(0);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_5);
x_111 = lean::apply_2(x_3, x_108, x_8);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; obj* x_113; obj* x_114; 
x_112 = lean::cnstr_get(x_111, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_113 = x_111;
} else {
 lean::dec_ref(x_111);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_110);
lean::cnstr_set(x_114, 1, x_112);
return x_114;
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_110);
x_115 = lean::cnstr_get(x_111, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_111, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_117 = x_111;
} else {
 lean::dec_ref(x_111);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_119 = lean::cnstr_get(x_107, 0);
lean::inc(x_119);
lean::dec(x_107);
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_119, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_122 = x_119;
} else {
 lean::dec_ref(x_119);
 x_122 = lean::box(0);
}
x_123 = l_List_reverse___rarg(x_121);
lean::inc(x_123);
lean::inc(x_3);
x_124 = l_List_mfor___main___at_Lean_runFrontend___spec__2(x_3, x_123, x_8);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_125 = lean::cnstr_get(x_124, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_126 = x_124;
} else {
 lean::dec_ref(x_124);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_11);
lean::cnstr_set(x_127, 1, x_125);
x_128 = lean::cnstr_get(x_10, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
lean::dec(x_128);
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
lean::dec(x_129);
x_131 = l_Lean_Expander_builtinTransformers;
lean::inc(x_130);
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::cnstr_get(x_130, 2);
lean::inc(x_133);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 lean::cnstr_release(x_130, 1);
 lean::cnstr_release(x_130, 2);
 x_134 = x_130;
} else {
 lean::dec_ref(x_130);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_1);
lean::cnstr_set(x_135, 1, x_2);
lean::cnstr_set(x_135, 2, x_133);
lean::inc(x_10);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_10);
x_137 = l_Lean_runFrontend___closed__1;
x_138 = l_Lean_Elaborator_mkState(x_136, x_5, x_137);
x_139 = lean::box(0);
if (lean::is_scalar(x_122)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_122;
}
lean::cnstr_set(x_140, 0, x_132);
lean::cnstr_set(x_140, 1, x_139);
x_141 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_141, 0, x_10);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_142, 0, x_138);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_120);
lean::cnstr_set(x_143, 1, x_142);
x_144 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_123, x_136, x_139, x_143, x_127);
return x_144;
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
lean::dec(x_123);
lean::dec(x_122);
lean::dec(x_120);
lean::dec(x_10);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_145 = lean::cnstr_get(x_124, 0);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_124, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_147 = x_124;
} else {
 lean::dec_ref(x_124);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_146);
return x_148;
}
}
}
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_149 = lean::cnstr_get(x_8, 0);
x_150 = lean::cnstr_get(x_8, 1);
lean::inc(x_150);
lean::inc(x_149);
lean::dec(x_8);
x_151 = lean::box(0);
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_150);
lean::inc(x_149);
x_153 = l_Lean_Parser_parseHeader(x_149);
x_154 = lean::cnstr_get(x_153, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 lean::cnstr_release(x_153, 1);
 x_155 = x_153;
} else {
 lean::dec_ref(x_153);
 x_155 = lean::box(0);
}
if (lean::obj_tag(x_154) == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_149);
lean::dec(x_2);
lean::dec(x_1);
x_156 = lean::cnstr_get(x_154, 0);
lean::inc(x_156);
lean::dec(x_154);
x_157 = lean::box(0);
if (lean::is_scalar(x_155)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_155;
}
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_5);
x_159 = lean::apply_2(x_3, x_156, x_152);
if (lean::obj_tag(x_159) == 0)
{
obj* x_160; obj* x_161; obj* x_162; 
x_160 = lean::cnstr_get(x_159, 1);
lean::inc(x_160);
if (lean::is_exclusive(x_159)) {
 lean::cnstr_release(x_159, 0);
 lean::cnstr_release(x_159, 1);
 x_161 = x_159;
} else {
 lean::dec_ref(x_159);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_160);
return x_162;
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_158);
x_163 = lean::cnstr_get(x_159, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_159, 1);
lean::inc(x_164);
if (lean::is_exclusive(x_159)) {
 lean::cnstr_release(x_159, 0);
 lean::cnstr_release(x_159, 1);
 x_165 = x_159;
} else {
 lean::dec_ref(x_159);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
lean::cnstr_set(x_166, 1, x_164);
return x_166;
}
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_167 = lean::cnstr_get(x_154, 0);
lean::inc(x_167);
lean::dec(x_154);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_167, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_170 = x_167;
} else {
 lean::dec_ref(x_167);
 x_170 = lean::box(0);
}
x_171 = l_List_reverse___rarg(x_169);
lean::inc(x_171);
lean::inc(x_3);
x_172 = l_List_mfor___main___at_Lean_runFrontend___spec__2(x_3, x_171, x_152);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_173 = lean::cnstr_get(x_172, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_174 = x_172;
} else {
 lean::dec_ref(x_172);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_151);
lean::cnstr_set(x_175, 1, x_173);
x_176 = lean::cnstr_get(x_149, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
lean::dec(x_176);
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
lean::dec(x_177);
x_179 = l_Lean_Expander_builtinTransformers;
lean::inc(x_178);
x_180 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_180, 0, x_178);
lean::cnstr_set(x_180, 1, x_179);
x_181 = lean::cnstr_get(x_178, 2);
lean::inc(x_181);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 x_182 = x_178;
} else {
 lean::dec_ref(x_178);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_1);
lean::cnstr_set(x_183, 1, x_2);
lean::cnstr_set(x_183, 2, x_181);
lean::inc(x_149);
x_184 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_149);
x_185 = l_Lean_runFrontend___closed__1;
x_186 = l_Lean_Elaborator_mkState(x_184, x_5, x_185);
x_187 = lean::box(0);
if (lean::is_scalar(x_170)) {
 x_188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_188 = x_170;
}
lean::cnstr_set(x_188, 0, x_180);
lean::cnstr_set(x_188, 1, x_187);
if (lean::is_scalar(x_155)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_155;
}
lean::cnstr_set(x_189, 0, x_149);
lean::cnstr_set(x_189, 1, x_188);
x_190 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_190, 0, x_186);
lean::cnstr_set(x_190, 1, x_189);
x_191 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_191, 0, x_168);
lean::cnstr_set(x_191, 1, x_190);
x_192 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_3, x_4, x_171, x_184, x_187, x_191, x_175);
return x_192;
}
else
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_171);
lean::dec(x_170);
lean::dec(x_168);
lean::dec(x_155);
lean::dec(x_149);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_193 = lean::cnstr_get(x_172, 0);
lean::inc(x_193);
x_194 = lean::cnstr_get(x_172, 1);
lean::inc(x_194);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_195 = x_172;
} else {
 lean::dec_ref(x_172);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
lean::cnstr_set(x_196, 1, x_194);
return x_196;
}
}
}
}
else
{
uint8 x_197; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_197 = !lean::is_exclusive(x_8);
if (x_197 == 0)
{
return x_8;
}
else
{
obj* x_198; obj* x_199; obj* x_200; 
x_198 = lean::cnstr_get(x_8, 0);
x_199 = lean::cnstr_get(x_8, 1);
lean::inc(x_199);
lean::inc(x_198);
lean::dec(x_8);
x_200 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_200, 0, x_198);
lean::cnstr_set(x_200, 1, x_199);
return x_200;
}
}
}
}
obj* l_ioOfExcept___at_Lean_runFrontend___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ioOfExcept___at_Lean_runFrontend___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__2(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___lambda__3(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_2);
lean::dec(x_2);
x_9 = l_IO_Prim_iterate___main___at_Lean_runFrontend___spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_Lean_runFrontend___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_4);
lean::dec(x_4);
x_8 = l_Lean_runFrontend(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", \"pos_col\": ");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", \"severity\": ");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("information");
x_2 = l_String_quote(x_1);
return x_2;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", \"caption\": ");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", \"text\": ");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("}");
return x_1;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("warning");
x_2 = l_String_quote(x_1);
return x_2;
}
}
obj* _init_l_Lean_processFile___lambda__1___closed__9() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("error");
x_2 = l_String_quote(x_1);
return x_2;
}
}
obj* l_Lean_processFile___lambda__1(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (x_1 == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Message_toString(x_2);
x_5 = l_IO_println___at_HasRepr_HasEval___spec__1(x_4, x_3);
lean::dec(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = l_Nat_repr(x_7);
x_9 = l_Lean_processFile___lambda__1___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_11 = l_Lean_processFile___lambda__1___closed__2;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Nat_repr(x_13);
x_15 = lean::string_append(x_12, x_14);
lean::dec(x_14);
x_16 = l_Lean_processFile___lambda__1___closed__3;
x_17 = lean::string_append(x_15, x_16);
x_18 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_19 = lean::cnstr_get(x_2, 3);
lean::inc(x_19);
x_20 = l_String_quote(x_19);
x_21 = lean::cnstr_get(x_2, 4);
lean::inc(x_21);
lean::dec(x_2);
x_22 = l_String_quote(x_21);
switch (x_18) {
case 0:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = l_Lean_processFile___lambda__1___closed__4;
x_24 = lean::string_append(x_17, x_23);
x_25 = l_Lean_processFile___lambda__1___closed__5;
x_26 = lean::string_append(x_24, x_25);
x_27 = lean::string_append(x_26, x_20);
lean::dec(x_20);
x_28 = l_Lean_processFile___lambda__1___closed__6;
x_29 = lean::string_append(x_27, x_28);
x_30 = lean::string_append(x_29, x_22);
lean::dec(x_22);
x_31 = l_Lean_processFile___lambda__1___closed__7;
x_32 = lean::string_append(x_30, x_31);
x_33 = l_IO_println___at_HasRepr_HasEval___spec__1(x_32, x_3);
lean::dec(x_32);
return x_33;
}
case 1:
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_34 = l_Lean_processFile___lambda__1___closed__8;
x_35 = lean::string_append(x_17, x_34);
x_36 = l_Lean_processFile___lambda__1___closed__5;
x_37 = lean::string_append(x_35, x_36);
x_38 = lean::string_append(x_37, x_20);
lean::dec(x_20);
x_39 = l_Lean_processFile___lambda__1___closed__6;
x_40 = lean::string_append(x_38, x_39);
x_41 = lean::string_append(x_40, x_22);
lean::dec(x_22);
x_42 = l_Lean_processFile___lambda__1___closed__7;
x_43 = lean::string_append(x_41, x_42);
x_44 = l_IO_println___at_HasRepr_HasEval___spec__1(x_43, x_3);
lean::dec(x_43);
return x_44;
}
default: 
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_45 = l_Lean_processFile___lambda__1___closed__9;
x_46 = lean::string_append(x_17, x_45);
x_47 = l_Lean_processFile___lambda__1___closed__5;
x_48 = lean::string_append(x_46, x_47);
x_49 = lean::string_append(x_48, x_20);
lean::dec(x_20);
x_50 = l_Lean_processFile___lambda__1___closed__6;
x_51 = lean::string_append(x_49, x_50);
x_52 = lean::string_append(x_51, x_22);
lean::dec(x_22);
x_53 = l_Lean_processFile___lambda__1___closed__7;
x_54 = lean::string_append(x_52, x_53);
x_55 = l_IO_println___at_HasRepr_HasEval___spec__1(x_54, x_3);
lean::dec(x_54);
return x_55;
}
}
}
}
}
obj* _init_l_Lean_processFile___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = lean::mk_nat_obj(1u);
x_2 = l_Nat_repr(x_1);
x_3 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string(", \"pos_col\": ");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Nat_repr(x_7);
x_9 = lean::string_append(x_6, x_8);
lean::dec(x_8);
x_10 = lean::mk_string(", \"severity\": ");
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
x_12 = lean::mk_string("error");
x_13 = l_String_quote(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
x_15 = lean::mk_string(", \"caption\": ");
x_16 = lean::string_append(x_14, x_15);
lean::dec(x_15);
x_17 = lean::mk_string("");
x_18 = l_String_quote(x_17);
x_19 = lean::string_append(x_16, x_18);
lean::dec(x_18);
x_20 = lean::mk_string(", \"text\": ");
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
return x_21;
}
}
obj* lean_process_file(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::box(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_processFile___lambda__1___boxed), 3, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = 0;
lean::inc(x_1);
x_9 = l_Lean_runFrontend(x_1, x_2, x_7, x_8, x_4, x_5);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_11, 0, x_14);
return x_9;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set(x_9, 0, x_17);
return x_9;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_9, 0);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_9);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_21 = x_18;
} else {
 lean::dec_ref(x_18);
 x_21 = lean::box(0);
}
x_22 = lean::box(0);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_9);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_9, 0);
x_27 = lean::box(0);
lean::cnstr_set_tag(x_9, 0);
lean::cnstr_set(x_9, 0, x_27);
if (x_3 == 0)
{
obj* x_28; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_28 = lean::box(0);
x_29 = l_Lean_Elaborator_notation_elaborate___closed__1;
x_30 = 2;
x_31 = l_String_splitAux___main___closed__1;
lean::inc(x_26);
x_32 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_28);
lean::cnstr_set(x_32, 3, x_31);
lean::cnstr_set(x_32, 4, x_26);
lean::cnstr_set_scalar(x_32, sizeof(void*)*5, x_30);
x_33 = l_Lean_Message_toString(x_32);
x_34 = l_IO_println___at_HasRepr_HasEval___spec__1(x_33, x_9);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_34);
if (x_35 == 0)
{
obj* x_36; 
x_36 = lean::cnstr_get(x_34, 0);
lean::dec(x_36);
lean::cnstr_set_tag(x_34, 1);
lean::cnstr_set(x_34, 0, x_26);
return x_34;
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_26);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8 x_39; 
lean::dec(x_26);
x_39 = !lean::is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_34, 0);
x_41 = lean::cnstr_get(x_34, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_34);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_1);
lean::inc(x_26);
x_43 = l_String_quote(x_26);
x_44 = l_Lean_processFile___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_46 = l_Lean_processFile___lambda__1___closed__7;
x_47 = lean::string_append(x_45, x_46);
x_48 = l_IO_println___at_HasRepr_HasEval___spec__1(x_47, x_9);
lean::dec(x_47);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_48);
if (x_49 == 0)
{
obj* x_50; 
x_50 = lean::cnstr_get(x_48, 0);
lean::dec(x_50);
lean::cnstr_set_tag(x_48, 1);
lean::cnstr_set(x_48, 0, x_26);
return x_48;
}
else
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_26);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8 x_53; 
lean::dec(x_26);
x_53 = !lean::is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_48, 0);
x_55 = lean::cnstr_get(x_48, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_48);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_9, 0);
x_58 = lean::cnstr_get(x_9, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_9);
x_59 = lean::box(0);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_58);
if (x_3 == 0)
{
obj* x_61; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_61 = lean::box(0);
x_62 = l_Lean_Elaborator_notation_elaborate___closed__1;
x_63 = 2;
x_64 = l_String_splitAux___main___closed__1;
lean::inc(x_57);
x_65 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_65, 0, x_1);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_61);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set(x_65, 4, x_57);
lean::cnstr_set_scalar(x_65, sizeof(void*)*5, x_63);
x_66 = l_Lean_Message_toString(x_65);
x_67 = l_IO_println___at_HasRepr_HasEval___spec__1(x_66, x_60);
lean::dec(x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_69 = x_67;
} else {
 lean::dec_ref(x_67);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_69;
 lean::cnstr_set_tag(x_70, 1);
}
lean::cnstr_set(x_70, 0, x_57);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_71 = lean::cnstr_get(x_67, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_73 = x_67;
} else {
 lean::dec_ref(x_67);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_1);
lean::inc(x_57);
x_75 = l_String_quote(x_57);
x_76 = l_Lean_processFile___closed__1;
x_77 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_78 = l_Lean_processFile___lambda__1___closed__7;
x_79 = lean::string_append(x_77, x_78);
x_80 = l_IO_println___at_HasRepr_HasEval___spec__1(x_79, x_60);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_80, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 lean::cnstr_release(x_80, 1);
 x_82 = x_80;
} else {
 lean::dec_ref(x_80);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_82;
 lean::cnstr_set_tag(x_83, 1);
}
lean::cnstr_set(x_83, 0, x_57);
lean::cnstr_set(x_83, 1, x_81);
return x_83;
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_57);
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_80, 1);
lean::inc(x_85);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 lean::cnstr_release(x_80, 1);
 x_86 = x_80;
} else {
 lean::dec_ref(x_80);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_85);
return x_87;
}
}
}
}
}
}
obj* l_Lean_processFile___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_processFile___lambda__1(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_processFile___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
lean::dec(x_3);
x_7 = lean_process_file(x_1, x_2, x_6, x_4, x_5);
return x_7;
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
