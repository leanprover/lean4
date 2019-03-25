// Lean compiler output
// Module: init.lean.format
// Imports: init.lean.options
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
obj* l_Lean_List_toFormat___main___rarg(obj*, obj*);
obj* l_Lean_KVMap_getNat(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_HasCoe(obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_toStringToFormat___rarg(obj*);
obj* l_Lean_Format_repr___main___closed__4;
obj* l_Lean_toFmt(obj*);
obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Format_indentOption___closed__1;
obj* l_Lean_Format_defIndent;
obj* l_Lean_Format_group___main(obj*);
obj* l_Lean_listHasToFormat___rarg(obj*);
obj* l_Lean_Format_prefixJoin___main(obj*);
obj* l_Lean_Format_joinSep___main___boxed(obj*);
obj* l_Lean_Format_spaceUptoLine___main___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_sbracket(obj*);
obj* l_Lean_Format_flatten(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_repr___main___closed__2;
obj* l_Lean_Format_spaceUptoLine_x_27___main___lambda__1___boxed(obj*, obj*, obj*);
uint8 l_Lean_Format_defUnicode;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_Lean_formatHasToString(obj*);
obj* l_Lean_Format_joinSep___main(obj*);
obj* l_Lean_formatHasToFormat;
obj* l_Lean_Format_spaceUptoLine___main___closed__2;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_Format_be(obj*, obj*, obj*, obj*);
obj* l_Lean_listHasToFormat___boxed(obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_toFmt___rarg(obj*, obj*);
obj* l_Lean_prodHasToFormat(obj*, obj*);
obj* l_Lean_Format_repr___main(obj*);
obj* l_Lean_Format_prefixJoin___main___boxed(obj*);
obj* l_Lean_Format_repr(obj*);
obj* l_Lean_Format_spaceUptoLine_x_27___main___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Format_join___closed__1;
obj* l_Lean_Format_joinSuffix(obj*);
obj* l_Lean_Format_repr___main___closed__3;
obj* l_Lean_Format_getUnicode___boxed(obj*);
uint8 l_Lean_KVMap_getBool(obj*, obj*, uint8);
obj* l_Nat_repr(obj*);
obj* l_Lean_Format_getWidth(obj*);
obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Format_getUnicode___closed__1;
obj* l_Lean_Format_defUnicode___boxed;
obj* l_Lean_toStringToFormat___boxed(obj*);
obj* l_Lean_Format_joinSuffix___boxed(obj*);
obj* l_Lean_toStringToFormat___rarg___lambda__1(obj*);
obj* l_Lean_natHasToFormat(obj*);
obj* l_Lean_Format_spaceUptoLine___main___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Format_be___main(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_nameHasToFormat(obj*);
obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_uint64HasToFormat(uint64);
obj* l_Lean_stringHasToFormat(obj*);
obj* l_Lean_Format_unicodeOption___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_toStringToFormat(obj*);
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_Lean_Format_joinSuffix___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_HasAppend(obj*, obj*);
obj* l_Lean_uint32HasToFormat(uint32);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerOption(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_Format_indentOption(obj*);
obj* l_Lean_Format_getIndent(obj*);
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_Lean_Format_flatten___main___closed__1;
obj* l_Lean_HasRepr___lambda__1(obj*);
obj* l_Lean_List_toFormat___main___rarg___closed__1;
obj* l_Lean_Format_joinSep(obj*);
obj* l_Lean_List_toFormat___main___rarg___closed__2;
obj* l_Lean_Format_getIndent___closed__1;
obj* l___private_init_lean_format_1__merge___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_widthOption___closed__1;
obj* l_Lean_Format_spaceUptoLine___main(obj*, obj*);
obj* l_Lean_usizeHasToFormat___boxed(obj*);
obj* l_Lean_uint32HasToFormat___boxed(obj*);
uint8 l_Lean_Format_getUnicode(obj*);
obj* l_Lean_prodHasToFormat___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_prefixJoin___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_spaceUptoLine_x_27___main(obj*, obj*);
obj* l_Lean_Format_joinSuffix___main(obj*);
obj* l_Lean_uint16HasToFormat(uint16);
obj* l_Lean_Format_sbracket___closed__3;
obj* l_List_foldl___main___at_Lean_Format_join___spec__1(obj*, obj*);
obj* l_Lean_Format_flatten___main(obj*);
obj* l_Lean_Format_prefixJoin___boxed(obj*);
obj* l_Lean_Format_repr___main___closed__7;
obj* l_Lean_Format_repr___main___closed__5;
obj* l_Lean_Format_paren(obj*);
obj* l_Lean_Format_group(obj*);
obj* l_Lean_Format_bracket(obj*, obj*, obj*);
obj* l___private_init_lean_format_1__merge(obj*, obj*, obj*);
obj* l_Lean_Format_defWidth;
obj* l_Lean_Format_unicodeOption(obj*);
obj* l_Lean_uint16HasToFormat___boxed(obj*);
obj* l_Lean_List_toFormat___rarg(obj*, obj*);
obj* l_Lean_List_toFormat___main___boxed(obj*);
obj* l_Lean_Format_prefixJoin(obj*);
obj* l_Lean_HasRepr;
obj* l_Lean_List_toFormat___boxed(obj*);
obj* l_Lean_toFmt___boxed(obj*);
obj* l_Lean_Format_widthOption(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_prodHasToFormat___boxed(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Format_prefixJoin___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_joinSuffix___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___boxed(obj*);
obj* l_Lean_Format_spaceUptoLine_x_27(obj*, obj*);
obj* l_Lean_Format_spaceUptoLine___main___closed__1;
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_Format_joinSep___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_joinSuffix___main___boxed(obj*);
obj* l_Lean_List_toFormat(obj*);
obj* l_String_quote(obj*);
obj* l_Lean_uint64HasToFormat___boxed(obj*);
namespace lean {
obj* usize_to_nat(usize);
}
extern obj* l_IO_println___rarg___closed__1;
obj* l_Lean_Format_spaceUptoLine(obj*, obj*);
obj* l_Lean_Format_repr___main___closed__1;
obj* l_Lean_Format_join(obj*);
obj* l_Lean_listHasToFormat(obj*);
obj* l_Lean_Format_repr___main___closed__6;
obj* l_Lean_usizeHasToFormat(usize);
obj* l_Lean_prodHasToFormat___rarg___closed__1;
obj* l_Lean_List_toFormat___main(obj*);
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Format_getWidth___closed__1;
obj* l_Lean_Format_HasAppend(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; obj* x_4; 
x_2 = 0;
x_3 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_2);
x_4 = x_3;
return x_4;
}
}
obj* l_Lean_Format_HasCoe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Format_join___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; uint8 x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = 0;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = x_8;
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_Format_join___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Format_join(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Format_join___closed__1;
x_2 = l_List_foldl___main___at_Lean_Format_join___spec__1(x_1, x_0);
return x_2;
}
}
obj* _init_l_Lean_Format_flatten___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Format_flatten___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; 
x_1 = l_Lean_Format_flatten___main___closed__1;
return x_1;
}
case 3:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
case 4:
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Format_flatten___main(x_7);
x_13 = l_Lean_Format_flatten___main(x_9);
x_14 = 1;
if (lean::is_scalar(x_11)) {
 x_15 = lean::alloc_cnstr(4, 2, 1);
} else {
 x_15 = x_11;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_14);
x_16 = x_15;
return x_16;
}
else
{
return x_0;
}
}
case 5:
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_0 = x_17;
goto _start;
}
default:
{
return x_0;
}
}
}
}
obj* l_Lean_Format_flatten(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_flatten___main(x_0);
return x_1;
}
}
obj* l_Lean_Format_group___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Format_flatten___main(x_0);
x_2 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
case 3:
{
obj* x_4; obj* x_5; 
lean::inc(x_0);
x_4 = l_Lean_Format_flatten___main(x_0);
x_5 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
}
case 4:
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_8; obj* x_9; 
lean::inc(x_0);
x_8 = l_Lean_Format_flatten___main(x_0);
x_9 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
return x_9;
}
else
{
return x_0;
}
}
case 5:
{
obj* x_11; obj* x_12; 
lean::inc(x_0);
x_11 = l_Lean_Format_flatten___main(x_0);
x_12 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
return x_12;
}
default:
{
return x_0;
}
}
}
}
obj* l_Lean_Format_group(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_group___main(x_0);
return x_1;
}
}
obj* l___private_init_lean_format_1__merge(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::thunk_get(x_2);
x_6 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1 + 1);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_12; uint8 x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_12 = lean::nat_add(x_8, x_9);
lean::dec(x_9);
x_14 = lean::nat_dec_lt(x_0, x_12);
x_15 = 0;
x_16 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = x_16;
lean::cnstr_set_scalar(x_17, sizeof(void*)*1 + 1, x_14);
x_18 = x_17;
return x_18;
}
else
{
return x_5;
}
}
else
{
return x_5;
}
}
else
{
lean::inc(x_1);
return x_1;
}
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l___private_init_lean_format_1__merge___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_format_1__merge(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine___main___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main(x_0, x_1);
return x_3;
}
}
obj* _init_l_Lean_Format_spaceUptoLine___main___closed__1() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = 0;
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set_scalar(x_2, sizeof(void*)*1, x_0);
x_3 = x_2;
lean::cnstr_set_scalar(x_3, sizeof(void*)*1 + 1, x_0);
x_4 = x_3;
return x_4;
}
}
obj* _init_l_Lean_Format_spaceUptoLine___main___closed__2() {
_start:
{
uint8 x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = 1;
x_1 = 0;
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_0);
x_4 = x_3;
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_1);
x_5 = x_4;
return x_5;
}
}
obj* l_Lean_Format_spaceUptoLine___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Lean_Format_spaceUptoLine___main___closed__1;
return x_3;
}
case 1:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_Lean_Format_spaceUptoLine___main___closed__2;
return x_5;
}
case 2:
{
obj* x_6; obj* x_9; uint8 x_11; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::string_length(x_6);
lean::dec(x_6);
x_11 = lean::nat_dec_lt(x_1, x_9);
lean::dec(x_1);
x_13 = 0;
x_14 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1, x_13);
x_15 = x_14;
lean::cnstr_set_scalar(x_15, sizeof(void*)*1 + 1, x_11);
x_16 = x_15;
return x_16;
}
case 4:
{
obj* x_17; obj* x_19; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
lean::inc(x_1);
x_23 = l_Lean_Format_spaceUptoLine___main(x_17, x_1);
lean::inc(x_1);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_spaceUptoLine___main___lambda__1___boxed), 3, 2);
lean::closure_set(x_25, 0, x_19);
lean::closure_set(x_25, 1, x_1);
x_26 = lean::mk_thunk(x_25);
x_27 = l___private_init_lean_format_1__merge(x_1, x_23, x_26);
lean::dec(x_26);
lean::dec(x_23);
lean::dec(x_1);
return x_27;
}
default:
{
obj* x_31; 
x_31 = lean::cnstr_get(x_0, 1);
lean::inc(x_31);
lean::dec(x_0);
x_0 = x_31;
goto _start;
}
}
}
}
obj* l_Lean_Format_spaceUptoLine___main___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_spaceUptoLine___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Format_spaceUptoLine_x_27___main___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x_27___main(x_0, x_1);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine_x_27___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Lean_Format_spaceUptoLine___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
lean::inc(x_1);
x_13 = l_Lean_Format_spaceUptoLine___main(x_9, x_1);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_spaceUptoLine_x_27___main___lambda__1___boxed), 3, 2);
lean::closure_set(x_15, 0, x_6);
lean::closure_set(x_15, 1, x_1);
x_16 = lean::mk_thunk(x_15);
x_17 = l___private_init_lean_format_1__merge(x_1, x_13, x_16);
lean::dec(x_16);
lean::dec(x_13);
lean::dec(x_1);
return x_17;
}
}
}
obj* l_Lean_Format_spaceUptoLine_x_27___main___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x_27___main___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_spaceUptoLine_x_27___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Format_be___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_6; obj* x_8; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_11; 
lean::dec(x_6);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
x_3 = x_11;
goto _start;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_22; obj* x_23; uint32 x_24; obj* x_26; 
lean::dec(x_1);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_6, 0);
lean::inc(x_19);
lean::dec(x_6);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean::string_append(x_2, x_22);
x_24 = 32;
lean::inc(x_19);
x_26 = l_Nat_repeatCore___main___at_String_pushn___spec__1(x_24, x_19, x_19, x_23);
x_1 = x_19;
x_2 = x_26;
x_3 = x_16;
goto _start;
}
case 2:
{
obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_39; 
lean::dec(x_6);
x_29 = lean::cnstr_get(x_3, 1);
lean::inc(x_29);
lean::dec(x_3);
x_32 = lean::cnstr_get(x_8, 0);
lean::inc(x_32);
lean::dec(x_8);
x_35 = lean::string_length(x_32);
x_36 = lean::nat_add(x_1, x_35);
lean::dec(x_35);
lean::dec(x_1);
x_39 = lean::string_append(x_2, x_32);
lean::dec(x_32);
x_1 = x_36;
x_2 = x_39;
x_3 = x_29;
goto _start;
}
case 3:
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_53; obj* x_56; obj* x_57; 
x_42 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_44 = x_3;
} else {
 lean::inc(x_42);
 lean::dec(x_3);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 1);
 x_47 = x_6;
} else {
 lean::inc(x_45);
 lean::dec(x_6);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_8, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_8, 1);
lean::inc(x_50);
lean::dec(x_8);
x_53 = lean::nat_add(x_45, x_48);
lean::dec(x_48);
lean::dec(x_45);
if (lean::is_scalar(x_47)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_47;
}
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_50);
if (lean::is_scalar(x_44)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_44;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_42);
x_3 = x_57;
goto _start;
}
case 4:
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_59 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 1);
 x_64 = x_6;
} else {
 lean::inc(x_62);
 lean::dec(x_6);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_8, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_8, 1);
lean::inc(x_67);
lean::dec(x_8);
lean::inc(x_62);
if (lean::is_scalar(x_64)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_64;
}
lean::cnstr_set(x_71, 0, x_62);
lean::cnstr_set(x_71, 1, x_65);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_62);
lean::cnstr_set(x_72, 1, x_67);
if (lean::is_scalar(x_61)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_61;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_59);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_73);
x_3 = x_74;
goto _start;
}
default:
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_89; obj* x_92; obj* x_93; obj* x_94; uint8 x_97; 
x_76 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_78 = x_3;
} else {
 lean::inc(x_76);
 lean::dec(x_3);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_release(x_6, 1);
 x_81 = x_6;
} else {
 lean::inc(x_79);
 lean::dec(x_6);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_8, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_8, 1);
lean::inc(x_84);
lean::dec(x_8);
lean::inc(x_0);
lean::inc(x_82);
x_89 = l_Lean_Format_spaceUptoLine___main(x_82, x_0);
lean::inc(x_0);
lean::inc(x_76);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_spaceUptoLine_x_27___main___lambda__1___boxed), 3, 2);
lean::closure_set(x_92, 0, x_76);
lean::closure_set(x_92, 1, x_0);
x_93 = lean::mk_thunk(x_92);
x_94 = l___private_init_lean_format_1__merge(x_0, x_89, x_93);
lean::dec(x_93);
lean::dec(x_89);
x_97 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1 + 1);
lean::dec(x_94);
if (x_97 == 0)
{
obj* x_100; obj* x_101; 
lean::dec(x_84);
if (lean::is_scalar(x_81)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_81;
}
lean::cnstr_set(x_100, 0, x_79);
lean::cnstr_set(x_100, 1, x_82);
if (lean::is_scalar(x_78)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_78;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_76);
x_3 = x_101;
goto _start;
}
else
{
obj* x_104; obj* x_105; 
lean::dec(x_82);
if (lean::is_scalar(x_81)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_81;
}
lean::cnstr_set(x_104, 0, x_79);
lean::cnstr_set(x_104, 1, x_84);
if (lean::is_scalar(x_78)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_78;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_76);
x_3 = x_105;
goto _start;
}
}
}
}
}
}
obj* l_Lean_Format_be(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Format_be___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_bracket(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::string_length(x_0);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_5);
x_7 = x_6;
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_2);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_5);
x_10 = x_9;
x_11 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Format_group___main(x_11);
return x_12;
}
}
obj* _init_l_Lean_Format_paren___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("(");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_paren___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(")");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_paren___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("(");
x_1 = lean::string_length(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_paren(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = 0;
x_2 = l_Lean_Format_paren___closed__1;
x_3 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_1);
x_4 = x_3;
x_5 = l_Lean_Format_paren___closed__2;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_1);
x_7 = x_6;
x_8 = l_Lean_Format_paren___closed__3;
x_9 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_Lean_Format_group___main(x_9);
return x_10;
}
}
obj* _init_l_Lean_Format_sbracket___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("[");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_sbracket___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("]");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_sbracket___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("[");
x_1 = lean::string_length(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_sbracket(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = 0;
x_2 = l_Lean_Format_sbracket___closed__1;
x_3 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_1);
x_4 = x_3;
x_5 = l_Lean_Format_sbracket___closed__2;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_1);
x_7 = x_6;
x_8 = l_Lean_Format_sbracket___closed__3;
x_9 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_Lean_Format_group___main(x_9);
return x_10;
}
}
obj* _init_l_Lean_Format_defIndent() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(4u);
return x_0;
}
}
uint8 _init_l_Lean_Format_defUnicode() {
_start:
{
uint8 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_Lean_Format_defUnicode___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_Lean_Format_defUnicode;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_defWidth() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(120u);
return x_0;
}
}
obj* _init_l_Lean_Format_getWidth___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("format");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("width");
x_4 = lean_name_mk_string(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_getWidth(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Format_getWidth___closed__1;
x_2 = l_Lean_Format_defWidth;
x_3 = l_Lean_KVMap_getNat(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Format_getIndent___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("format");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("indent");
x_4 = lean_name_mk_string(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_getIndent(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Format_getIndent___closed__1;
x_2 = l_Lean_Format_defIndent;
x_3 = l_Lean_KVMap_getNat(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Format_getUnicode___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("format");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("unicode");
x_4 = lean_name_mk_string(x_2, x_3);
return x_4;
}
}
uint8 l_Lean_Format_getUnicode(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; uint8 x_3; 
x_1 = l_Lean_Format_getUnicode___closed__1;
x_2 = l_Lean_Format_defUnicode;
x_3 = l_Lean_KVMap_getBool(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_getUnicode___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Format_getUnicode(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_indentOption___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Lean_Format_defIndent;
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string("format");
x_3 = lean::mk_string("indentation");
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Lean_Format_indentOption(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Format_getIndent___closed__1;
x_2 = l_Lean_Format_indentOption___closed__1;
x_3 = l_Lean_registerOption(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Format_unicodeOption___closed__1() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_Lean_Format_defUnicode;
x_1 = lean::alloc_cnstr(1, 0, 1);
lean::cnstr_set_scalar(x_1, 0, x_0);
x_2 = x_1;
x_3 = lean::mk_string("format");
x_4 = lean::mk_string("unicode characters");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* l_Lean_Format_unicodeOption(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Format_getUnicode___closed__1;
x_2 = l_Lean_Format_unicodeOption___closed__1;
x_3 = l_Lean_registerOption(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Format_widthOption___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Lean_Format_defWidth;
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string("format");
x_3 = lean::mk_string("line width");
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Lean_Format_widthOption(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Format_getWidth___closed__1;
x_2 = l_Lean_Format_widthOption___closed__1;
x_3 = l_Lean_registerOption(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Lean_Format_pretty(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_defWidth;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_String_splitAux___main___closed__1;
x_10 = l_Lean_Format_be___main(x_4, x_5, x_9, x_8);
return x_10;
}
}
obj* l_Lean_toFmt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_Lean_toFmt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_toFmt___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_toFmt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_toFmt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_toStringToFormat___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_toStringToFormat___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_toStringToFormat___rarg___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_1);
lean::closure_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_Lean_toStringToFormat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_toStringToFormat___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_toStringToFormat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_toStringToFormat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_formatHasToFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_stringHasToFormat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Format_joinSep___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_12; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::apply_1(x_0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_17; uint8 x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_0);
x_17 = lean::apply_1(x_0, x_13);
x_18 = 0;
lean::inc(x_2);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_18);
x_21 = x_20;
x_22 = l_Lean_Format_joinSep___main___rarg(x_0, x_6, x_2);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_18);
x_24 = x_23;
return x_24;
}
}
}
}
obj* l_Lean_Format_joinSep___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSep___main___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_joinSep___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_joinSep___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_joinSep___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_joinSep___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_joinSep(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSep___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_joinSep___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_joinSep(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_prefixJoin___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; uint8 x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = 0;
lean::inc(x_1);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = l_Lean_Format_prefixJoin___main___rarg(x_0, x_1, x_8);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_13);
x_19 = x_18;
return x_19;
}
}
}
obj* l_Lean_Format_prefixJoin___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_prefixJoin___main___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_prefixJoin___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_prefixJoin___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_prefixJoin___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_prefixJoin___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_prefixJoin(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_prefixJoin___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_prefixJoin___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_prefixJoin(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_joinSuffix___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; uint8 x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = 0;
lean::inc(x_2);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_2);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = l_Lean_Format_joinSuffix___main___rarg(x_0, x_8, x_2);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_13);
x_19 = x_18;
return x_19;
}
}
}
obj* l_Lean_Format_joinSuffix___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSuffix___main___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_joinSuffix___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_joinSuffix___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Format_joinSuffix___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_joinSuffix___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_joinSuffix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSuffix___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Format_joinSuffix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_joinSuffix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_List_toFormat___main___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("[]");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_List_toFormat___main___rarg___closed__2() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string(",");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 0;
x_3 = lean::box(1);
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
return x_5;
}
}
obj* l_Lean_List_toFormat___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_Lean_List_toFormat___main___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_4 = l_Lean_List_toFormat___main___rarg___closed__2;
x_5 = l_Lean_Format_joinSep___main___rarg(x_0, x_1, x_4);
x_6 = 0;
x_7 = l_Lean_Format_sbracket___closed__1;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = x_8;
x_10 = l_Lean_Format_sbracket___closed__2;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_6);
x_12 = x_11;
x_13 = l_Lean_Format_sbracket___closed__3;
x_14 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_Lean_Format_group___main(x_14);
return x_15;
}
}
}
obj* l_Lean_List_toFormat___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_toFormat___main___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_List_toFormat___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_List_toFormat___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_List_toFormat___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_List_toFormat___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_List_toFormat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_toFormat___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_List_toFormat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_List_toFormat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_listHasToFormat___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_toFormat___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_listHasToFormat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_listHasToFormat___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_listHasToFormat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_listHasToFormat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_prodHasToFormat___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(",");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_prodHasToFormat___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = 0;
x_10 = l_Lean_prodHasToFormat___rarg___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = lean::box(1);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::apply_1(x_1, x_5);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_9);
x_18 = x_17;
x_19 = l_Lean_Format_paren___closed__1;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_9);
x_21 = x_20;
x_22 = l_Lean_Format_paren___closed__2;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_9);
x_24 = x_23;
x_25 = l_Lean_Format_paren___closed__3;
x_26 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = l_Lean_Format_group___main(x_26);
return x_27;
}
}
obj* l_Lean_prodHasToFormat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_prodHasToFormat___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_prodHasToFormat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_prodHasToFormat(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_natHasToFormat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_uint16HasToFormat(uint16 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::uint16_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_uint16HasToFormat___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_uint16HasToFormat(x_1);
return x_2;
}
}
obj* l_Lean_uint32HasToFormat(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_uint32HasToFormat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Lean_uint32HasToFormat(x_1);
return x_2;
}
}
obj* l_Lean_uint64HasToFormat(uint64 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::uint64_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_uint64HasToFormat___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = l_Lean_uint64HasToFormat(x_1);
return x_2;
}
}
obj* l_Lean_usizeHasToFormat(usize x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::usize_to_nat(x_0);
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_usizeHasToFormat___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = l_Lean_usizeHasToFormat(x_1);
return x_2;
}
}
obj* l_Lean_nameHasToFormat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = l_Lean_Name_toStringWithSep___main(x_1, x_0);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_Format_repr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("Format.nil");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_repr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("Format.line");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Format_repr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string("Format.text");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 0;
x_3 = lean::box(1);
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
return x_5;
}
}
obj* _init_l_Lean_Format_repr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string("Format.nest");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 0;
x_3 = lean::box(1);
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
return x_5;
}
}
obj* _init_l_Lean_Format_repr___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("Format.compose ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string("false");
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = 0;
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_4);
x_6 = x_5;
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_4);
x_9 = x_8;
return x_9;
}
}
obj* _init_l_Lean_Format_repr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("Format.compose ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::mk_string("true");
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = 0;
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_4);
x_6 = x_5;
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_4);
x_9 = x_8;
return x_9;
}
}
obj* _init_l_Lean_Format_repr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string("Format.choice");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 0;
x_3 = lean::box(1);
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
return x_5;
}
}
obj* l_Lean_Format_repr___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = l_Lean_Format_repr___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = l_Lean_Format_repr___main___closed__2;
return x_2;
}
case 2:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = l_String_quote(x_3);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
x_8 = 0;
x_9 = l_Lean_Format_repr___main___closed__3;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = x_10;
x_12 = l_Lean_Format_paren___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_8);
x_14 = x_13;
x_15 = l_Lean_Format_paren___closed__2;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_8);
x_17 = x_16;
x_18 = l_Lean_Format_paren___closed__3;
x_19 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_Lean_Format_group___main(x_19);
return x_20;
}
case 3:
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_21 = lean::cnstr_get(x_0, 0);
x_23 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_25 = x_0;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_0);
 x_25 = lean::box(0);
}
x_26 = l_Nat_repr(x_21);
x_27 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = 0;
x_29 = l_Lean_Format_repr___main___closed__4;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_28);
x_31 = x_30;
x_32 = lean::box(1);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_28);
x_34 = x_33;
x_35 = l_Lean_Format_repr___main(x_23);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_28);
x_37 = x_36;
x_38 = l_Lean_Format_paren___closed__1;
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_28);
x_40 = x_39;
x_41 = l_Lean_Format_paren___closed__2;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_28);
x_43 = x_42;
x_44 = l_Lean_Format_paren___closed__3;
if (lean::is_scalar(x_25)) {
 x_45 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_45 = x_25;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
x_46 = l_Lean_Format_group___main(x_45);
return x_46;
}
case 4:
{
uint8 x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_48 = lean::cnstr_get(x_0, 0);
x_50 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_52 = x_0;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_0);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Format_repr___main(x_48);
x_54 = l_Lean_Format_repr___main(x_50);
if (x_47 == 0)
{
uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_55 = 0;
x_56 = l_Lean_Format_repr___main___closed__5;
if (lean::is_scalar(x_52)) {
 x_57 = lean::alloc_cnstr(4, 2, 1);
} else {
 x_57 = x_52;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_55);
x_58 = x_57;
x_59 = lean::box(1);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_55);
x_61 = x_60;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_55);
x_63 = x_62;
x_64 = l_Lean_Format_paren___closed__1;
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_55);
x_66 = x_65;
x_67 = l_Lean_Format_paren___closed__2;
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_55);
x_69 = x_68;
x_70 = l_Lean_Format_paren___closed__3;
x_71 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_69);
x_72 = l_Lean_Format_group___main(x_71);
return x_72;
}
else
{
uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_73 = 0;
x_74 = l_Lean_Format_repr___main___closed__6;
if (lean::is_scalar(x_52)) {
 x_75 = lean::alloc_cnstr(4, 2, 1);
} else {
 x_75 = x_52;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_53);
lean::cnstr_set_scalar(x_75, sizeof(void*)*2, x_73);
x_76 = x_75;
x_77 = lean::box(1);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_73);
x_79 = x_78;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_54);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_73);
x_81 = x_80;
x_82 = l_Lean_Format_paren___closed__1;
x_83 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_81);
lean::cnstr_set_scalar(x_83, sizeof(void*)*2, x_73);
x_84 = x_83;
x_85 = l_Lean_Format_paren___closed__2;
x_86 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_85);
lean::cnstr_set_scalar(x_86, sizeof(void*)*2, x_73);
x_87 = x_86;
x_88 = l_Lean_Format_paren___closed__3;
x_89 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_87);
x_90 = l_Lean_Format_group___main(x_89);
return x_90;
}
}
default:
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_91 = lean::cnstr_get(x_0, 0);
x_93 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_95 = x_0;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_0);
 x_95 = lean::box(0);
}
x_96 = l_Lean_Format_repr___main(x_91);
x_97 = 0;
x_98 = l_Lean_Format_repr___main___closed__7;
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_97);
x_100 = x_99;
x_101 = lean::box(1);
x_102 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_101);
lean::cnstr_set_scalar(x_102, sizeof(void*)*2, x_97);
x_103 = x_102;
x_104 = l_Lean_Format_repr___main(x_93);
x_105 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*2, x_97);
x_106 = x_105;
x_107 = l_Lean_Format_paren___closed__1;
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_106);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_97);
x_109 = x_108;
x_110 = l_Lean_Format_paren___closed__2;
x_111 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_111, 0, x_109);
lean::cnstr_set(x_111, 1, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*2, x_97);
x_112 = x_111;
x_113 = l_Lean_Format_paren___closed__3;
if (lean::is_scalar(x_95)) {
 x_114 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_114 = x_95;
 lean::cnstr_set_tag(x_95, 3);
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_112);
x_115 = l_Lean_Format_group___main(x_114);
return x_115;
}
}
}
}
obj* l_Lean_Format_repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Format_repr___main(x_0);
return x_1;
}
}
obj* l_Lean_formatHasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Options_empty;
x_2 = l_Lean_Format_pretty(x_0, x_1);
return x_2;
}
}
obj* l_Lean_HasRepr___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Options_empty;
x_2 = l_Lean_Format_pretty(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_HasRepr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_HasRepr___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_repr), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* initialize_init_lean_options(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_format(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_options(w);
 l_Lean_Format_join___closed__1 = _init_l_Lean_Format_join___closed__1();
lean::mark_persistent(l_Lean_Format_join___closed__1);
 l_Lean_Format_flatten___main___closed__1 = _init_l_Lean_Format_flatten___main___closed__1();
lean::mark_persistent(l_Lean_Format_flatten___main___closed__1);
 l_Lean_Format_spaceUptoLine___main___closed__1 = _init_l_Lean_Format_spaceUptoLine___main___closed__1();
lean::mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__1);
 l_Lean_Format_spaceUptoLine___main___closed__2 = _init_l_Lean_Format_spaceUptoLine___main___closed__2();
lean::mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__2);
 l_Lean_Format_paren___closed__1 = _init_l_Lean_Format_paren___closed__1();
lean::mark_persistent(l_Lean_Format_paren___closed__1);
 l_Lean_Format_paren___closed__2 = _init_l_Lean_Format_paren___closed__2();
lean::mark_persistent(l_Lean_Format_paren___closed__2);
 l_Lean_Format_paren___closed__3 = _init_l_Lean_Format_paren___closed__3();
lean::mark_persistent(l_Lean_Format_paren___closed__3);
 l_Lean_Format_sbracket___closed__1 = _init_l_Lean_Format_sbracket___closed__1();
lean::mark_persistent(l_Lean_Format_sbracket___closed__1);
 l_Lean_Format_sbracket___closed__2 = _init_l_Lean_Format_sbracket___closed__2();
lean::mark_persistent(l_Lean_Format_sbracket___closed__2);
 l_Lean_Format_sbracket___closed__3 = _init_l_Lean_Format_sbracket___closed__3();
lean::mark_persistent(l_Lean_Format_sbracket___closed__3);
 l_Lean_Format_defIndent = _init_l_Lean_Format_defIndent();
lean::mark_persistent(l_Lean_Format_defIndent);
 l_Lean_Format_defUnicode = _init_l_Lean_Format_defUnicode();
 l_Lean_Format_defUnicode___boxed = _init_l_Lean_Format_defUnicode___boxed();
lean::mark_persistent(l_Lean_Format_defUnicode___boxed);
 l_Lean_Format_defWidth = _init_l_Lean_Format_defWidth();
lean::mark_persistent(l_Lean_Format_defWidth);
 l_Lean_Format_getWidth___closed__1 = _init_l_Lean_Format_getWidth___closed__1();
lean::mark_persistent(l_Lean_Format_getWidth___closed__1);
 l_Lean_Format_getIndent___closed__1 = _init_l_Lean_Format_getIndent___closed__1();
lean::mark_persistent(l_Lean_Format_getIndent___closed__1);
 l_Lean_Format_getUnicode___closed__1 = _init_l_Lean_Format_getUnicode___closed__1();
lean::mark_persistent(l_Lean_Format_getUnicode___closed__1);
 l_Lean_Format_indentOption___closed__1 = _init_l_Lean_Format_indentOption___closed__1();
lean::mark_persistent(l_Lean_Format_indentOption___closed__1);
w = l_Lean_Format_indentOption(w);
if (io_result_is_error(w)) return w;
 l_Lean_Format_unicodeOption___closed__1 = _init_l_Lean_Format_unicodeOption___closed__1();
lean::mark_persistent(l_Lean_Format_unicodeOption___closed__1);
w = l_Lean_Format_unicodeOption(w);
if (io_result_is_error(w)) return w;
 l_Lean_Format_widthOption___closed__1 = _init_l_Lean_Format_widthOption___closed__1();
lean::mark_persistent(l_Lean_Format_widthOption___closed__1);
w = l_Lean_Format_widthOption(w);
if (io_result_is_error(w)) return w;
 l_Lean_formatHasToFormat = _init_l_Lean_formatHasToFormat();
lean::mark_persistent(l_Lean_formatHasToFormat);
 l_Lean_List_toFormat___main___rarg___closed__1 = _init_l_Lean_List_toFormat___main___rarg___closed__1();
lean::mark_persistent(l_Lean_List_toFormat___main___rarg___closed__1);
 l_Lean_List_toFormat___main___rarg___closed__2 = _init_l_Lean_List_toFormat___main___rarg___closed__2();
lean::mark_persistent(l_Lean_List_toFormat___main___rarg___closed__2);
 l_Lean_prodHasToFormat___rarg___closed__1 = _init_l_Lean_prodHasToFormat___rarg___closed__1();
lean::mark_persistent(l_Lean_prodHasToFormat___rarg___closed__1);
 l_Lean_Format_repr___main___closed__1 = _init_l_Lean_Format_repr___main___closed__1();
lean::mark_persistent(l_Lean_Format_repr___main___closed__1);
 l_Lean_Format_repr___main___closed__2 = _init_l_Lean_Format_repr___main___closed__2();
lean::mark_persistent(l_Lean_Format_repr___main___closed__2);
 l_Lean_Format_repr___main___closed__3 = _init_l_Lean_Format_repr___main___closed__3();
lean::mark_persistent(l_Lean_Format_repr___main___closed__3);
 l_Lean_Format_repr___main___closed__4 = _init_l_Lean_Format_repr___main___closed__4();
lean::mark_persistent(l_Lean_Format_repr___main___closed__4);
 l_Lean_Format_repr___main___closed__5 = _init_l_Lean_Format_repr___main___closed__5();
lean::mark_persistent(l_Lean_Format_repr___main___closed__5);
 l_Lean_Format_repr___main___closed__6 = _init_l_Lean_Format_repr___main___closed__6();
lean::mark_persistent(l_Lean_Format_repr___main___closed__6);
 l_Lean_Format_repr___main___closed__7 = _init_l_Lean_Format_repr___main___closed__7();
lean::mark_persistent(l_Lean_Format_repr___main___closed__7);
 l_Lean_HasRepr = _init_l_Lean_HasRepr();
lean::mark_persistent(l_Lean_HasRepr);
return w;
}
