// Lean compiler output
// Module: init.lean.format
// Imports: init.lean.options init.data.array.default
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
obj* l_Lean_uint32HasFormat___boxed(obj*);
obj* l_Lean_KVMap_getNat(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(obj*, obj*);
obj* l_Lean_formatDataValue___main(obj*);
obj* l_Lean_dataValueHasFormat;
obj* l_Lean_Format_joinSep___main___rarg(obj*, obj*, obj*);
obj* l_Lean_formatKVMap(obj*);
obj* l_Lean_Format_HasCoe(obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_toStringToFormat___rarg(obj*);
obj* l_Lean_Format_repr___main___closed__4;
obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Format_indentOption___closed__1;
obj* l_Lean_Format_defIndent;
obj* l_Nat_repeatAux___main___at_String_pushn___spec__1(uint32, obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l_Lean_Format_prefixJoin___main(obj*);
obj* l_Lean_stringHasFormat(obj*);
obj* l_Lean_formatDataValue___main___closed__1;
obj* l_Lean_Format_spaceUptoLine_x27___boxed(obj*, obj*);
obj* l_Lean_List_format___main___rarg(obj*, obj*);
obj* l_Lean_nameHasFormat(obj*);
obj* l_Lean_Format_sbracket(obj*);
obj* l_Lean_Format_flatten(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_be___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_repr___main___closed__2;
uint8 l_Lean_Format_defUnicode;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_Lean_formatHasToString(obj*);
obj* l_Lean_Format_joinSep___main(obj*);
obj* l_Lean_Format_getWidth___boxed(obj*);
obj* l_Lean_Format_joinArraySep___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_spaceUptoLine___main___closed__2;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_Format_be(obj*, obj*, obj*, obj*);
uint8 l_Lean_Format_isNil___main(obj*);
obj* l_Lean_fmt(obj*);
obj* l_Lean_entryHasFormat;
namespace lean {
obj* format_append_core(obj*, obj*);
}
extern obj* l_Lean_Options_empty;
obj* l_Lean_Format_getIndent___boxed(obj*);
obj* l_Lean_Format_repr___main(obj*);
obj* l_Lean_Format_repr(obj*);
obj* l_Lean_uint64HasFormat___boxed(obj*);
obj* l_Lean_Format_join___closed__1;
obj* l_Lean_Format_joinSuffix(obj*);
obj* l_Lean_Format_repr___main___closed__3;
obj* l_Lean_Format_getUnicode___boxed(obj*);
uint8 l_Lean_KVMap_getBool(obj*, obj*, uint8);
obj* l_Nat_repr(obj*);
obj* l_Lean_Format_getWidth(obj*);
obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Format_getUnicode___closed__1;
obj* l_Lean_Format_joinArraySep(obj*);
obj* l_Lean_toStringToFormat___rarg___closed__1;
obj* l_Lean_prodHasFormat___rarg___closed__1;
obj* l_Lean_uint64HasFormat(uint64);
obj* l_Lean_toStringToFormat___rarg___lambda__1(obj*);
obj* l_Lean_List_format___main(obj*);
obj* l_Lean_Format_be___main(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_fmt___rarg(obj*, obj*);
obj* l_Lean_formatDataValue(obj*);
obj* l_Lean_Format_unicodeOption___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_toStringToFormat(obj*);
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_Lean_List_format___rarg(obj*, obj*);
obj* l_Lean_Format_joinSuffix___rarg(obj*, obj*, obj*);
obj* l_Int_repr___main(obj*);
obj* l_Lean_Format_HasAppend;
obj* l_List_foldl___main___at_Lean_Format_join___spec__1___boxed(obj*, obj*);
obj* l_Lean_formatEntry(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_List_format___main___rarg___closed__1;
obj* l_Lean_natHasFormat(obj*);
obj* l_Lean_registerOption(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Format_spaceUptoLine___main___boxed(obj*, obj*);
obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_Format_Inhabited;
obj* l_Lean_Format_indentOption(obj*);
obj* l_Lean_Format_spaceUptoLine___boxed(obj*, obj*);
obj* l_Lean_formatEntry___main___closed__1;
obj* l_Lean_Format_getIndent(obj*);
obj* l_Lean_Format_flatten___main___closed__1;
obj* l_Lean_HasRepr___lambda__1(obj*);
obj* l_Lean_listHasFormat___rarg(obj*);
obj* l_Lean_prodHasFormat(obj*, obj*);
obj* l_Lean_Format_joinSep(obj*);
obj* l_Lean_Format_joinArraySep___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_getIndent___closed__1;
obj* l___private_init_lean_format_1__merge___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_widthOption___closed__1;
obj* l_Lean_uint16HasFormat___boxed(obj*);
obj* l_Lean_Format_spaceUptoLine___main(obj*, obj*);
obj* l_Lean_formatHasFormat;
uint8 l_Lean_Format_getUnicode(obj*);
obj* l_Lean_Format_prefixJoin___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_spaceUptoLine_x27___main(obj*, obj*);
obj* l_Lean_Format_joinSuffix___main(obj*);
obj* l_Lean_prodHasFormat___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_sbracket___closed__3;
obj* l_List_foldl___main___at_Lean_Format_join___spec__1(obj*, obj*);
obj* l_Lean_Format_flatten___main(obj*);
obj* l_Lean_uint32HasFormat(uint32);
obj* l_Lean_formatKVMap___closed__1;
obj* l_Lean_Format_repr___main___closed__7;
obj* l_Lean_Format_repr___main___closed__5;
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1(obj*);
obj* l_Lean_Format_paren(obj*);
obj* l_Lean_Format_isNil___main___boxed(obj*);
obj* l_Lean_usizeHasFormat(usize);
namespace lean {
obj* format_group_core(obj*);
}
obj* l_Lean_Format_bracket(obj*, obj*, obj*);
obj* l_Lean_listHasFormat(obj*);
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_format_1__merge(obj*, obj*, obj*);
obj* l_Lean_Format_be___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_spaceUptoLine_x27___main___boxed(obj*, obj*);
obj* l_Lean_Format_defWidth;
obj* l_Lean_Format_unicodeOption(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Format_prefixJoin(obj*);
obj* l_Lean_HasRepr;
obj* l_Lean_List_format(obj*);
obj* l_Lean_usizeHasFormat___boxed(obj*);
obj* l_Lean_formatDataValue___main___closed__3;
obj* l_Lean_Format_widthOption(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Format_prefixJoin___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_joinSuffix___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Format_isNil___boxed(obj*);
obj* l_Lean_Format_pretty___boxed(obj*, obj*);
obj* l_Lean_Format_spaceUptoLine_x27(obj*, obj*);
obj* l_Lean_Format_spaceUptoLine___main___closed__1;
namespace lean {
obj* uint32_to_nat(uint32);
}
uint8 l_Lean_Format_isNil(obj*);
obj* l_Lean_Format_joinSep___rarg(obj*, obj*, obj*);
obj* l_String_quote(obj*);
namespace lean {
obj* format_pretty_core(obj*, obj*);
}
obj* l_Lean_formatDataValue___main___closed__2;
obj* l_Lean_Format_join___boxed(obj*);
namespace lean {
obj* usize_to_nat(usize);
}
extern obj* l_IO_println___rarg___closed__1;
obj* l_Thunk_get(obj*, obj*);
obj* l_Lean_formatEntry___main(obj*);
obj* l_Lean_Format_spaceUptoLine(obj*, obj*);
obj* l_Lean_kvMapHasFormat;
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Format_repr___main___closed__1;
obj* l_Lean_uint16HasFormat(uint16);
obj* l_Lean_Format_join(obj*);
obj* l_Lean_Format_repr___main___closed__6;
obj* l_Lean_List_format___main___rarg___closed__2;
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Format_getWidth___closed__1;
namespace lean {
obj* format_append_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = 0;
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
}
obj* _init_l_Lean_Format_HasAppend() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(lean::format_append_core), 2, 0);
return x_1;
}
}
obj* l_Lean_Format_HasCoe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_Inhabited() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Format_join___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = 0;
lean::inc(x_3);
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_Format_join___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Format_join(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Format_join___closed__1;
x_3 = l_List_foldl___main___at_Lean_Format_join___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_List_foldl___main___at_Lean_Format_join___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Format_join___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Format_join___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_join(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_Format_isNil___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Lean_Format_isNil___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Format_isNil___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Format_isNil(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Format_isNil___main(x_1);
return x_2;
}
}
obj* l_Lean_Format_isNil___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Format_isNil(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_Format_flatten___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Format_flatten___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; 
x_2 = l_Lean_Format_flatten___main___closed__1;
return x_2;
}
case 3:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_1 = x_3;
goto _start;
}
case 4:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = l_Lean_Format_flatten___main(x_7);
x_10 = l_Lean_Format_flatten___main(x_8);
x_11 = 1;
lean::cnstr_set(x_1, 1, x_10);
lean::cnstr_set(x_1, 0, x_9);
lean::cnstr_set_scalar(x_1, sizeof(void*)*2, x_11);
return x_1;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = l_Lean_Format_flatten___main(x_12);
x_15 = l_Lean_Format_flatten___main(x_13);
x_16 = 1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_16);
return x_17;
}
}
else
{
return x_1;
}
}
case 5:
{
obj* x_18; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_1 = x_18;
goto _start;
}
default: 
{
return x_1;
}
}
}
}
obj* l_Lean_Format_flatten(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_flatten___main(x_1);
return x_2;
}
}
obj* l_Lean_Format_group___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 2:
{
return x_1;
}
case 4:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = l_Lean_Format_flatten___main(x_1);
x_4 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
return x_1;
}
}
default: 
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = l_Lean_Format_flatten___main(x_1);
x_6 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
}
}
namespace lean {
obj* format_group_core(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_group___main(x_1);
return x_2;
}
}
}
obj* l___private_init_lean_format_1__merge(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1 + 1);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::thunk_get_own(x_3);
x_7 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1 + 1);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; uint8 x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_10);
x_12 = lean::nat_dec_lt(x_1, x_11);
x_13 = 0;
x_14 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1 + 1, x_12);
return x_14;
}
else
{
return x_6;
}
}
else
{
return x_6;
}
}
else
{
lean::inc(x_2);
return x_2;
}
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l___private_init_lean_format_1__merge___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_format_1__merge(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Format_spaceUptoLine___main___closed__1() {
_start:
{
uint8 x_1; obj* x_2; obj* x_3; 
x_1 = 0;
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1 + 1, x_1);
return x_3;
}
}
obj* _init_l_Lean_Format_spaceUptoLine___main___closed__2() {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_2);
return x_4;
}
}
obj* l_Lean_Format_spaceUptoLine___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main___closed__1;
return x_3;
}
case 1:
{
obj* x_4; 
x_4 = l_Lean_Format_spaceUptoLine___main___closed__2;
return x_4;
}
case 2:
{
obj* x_5; obj* x_6; uint8 x_7; uint8 x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::string_length(x_5);
x_7 = lean::nat_dec_lt(x_2, x_6);
x_8 = 0;
x_9 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1 + 1, x_7);
return x_9;
}
case 4:
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = l_Lean_Format_spaceUptoLine___main(x_10, x_2);
x_13 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1 + 1);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = l_Lean_Format_spaceUptoLine___main(x_11, x_2);
x_16 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1 + 1);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; uint8 x_21; uint8 x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::nat_add(x_18, x_19);
lean::dec(x_19);
lean::dec(x_18);
x_21 = lean::nat_dec_lt(x_2, x_20);
x_22 = 0;
x_23 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set_scalar(x_23, sizeof(void*)*1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*1 + 1, x_21);
return x_23;
}
else
{
lean::dec(x_12);
return x_15;
}
}
else
{
lean::dec(x_12);
return x_15;
}
}
else
{
return x_12;
}
}
else
{
return x_12;
}
}
default: 
{
obj* x_24; 
x_24 = lean::cnstr_get(x_1, 1);
x_1 = x_24;
goto _start;
}
}
}
}
obj* l_Lean_Format_spaceUptoLine___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine_x27___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 1);
x_7 = l_Lean_Format_spaceUptoLine___main(x_6, x_2);
x_8 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1 + 1);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = l_Lean_Format_spaceUptoLine_x27___main(x_5, x_2);
x_11 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1 + 1);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; uint8 x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_15 = lean::nat_add(x_13, x_14);
lean::dec(x_14);
lean::dec(x_13);
x_16 = lean::nat_dec_lt(x_2, x_15);
x_17 = 0;
x_18 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1 + 1, x_16);
return x_18;
}
else
{
lean::dec(x_7);
return x_10;
}
}
else
{
lean::dec(x_7);
return x_10;
}
}
else
{
return x_7;
}
}
else
{
return x_7;
}
}
}
}
obj* l_Lean_Format_spaceUptoLine_x27___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine_x27(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Format_spaceUptoLine_x27___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_spaceUptoLine_x27(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Format_be___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_7; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_4 = x_7;
goto _start;
}
case 1:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; obj* x_14; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = l_IO_println___rarg___closed__1;
x_12 = lean::string_append(x_3, x_11);
x_13 = 32;
lean::inc(x_10);
x_14 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_13, x_10, x_12);
x_2 = x_10;
x_3 = x_14;
x_4 = x_9;
goto _start;
}
case 2:
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_18 = lean::string_length(x_17);
x_19 = lean::nat_add(x_2, x_18);
lean::dec(x_18);
lean::dec(x_2);
x_20 = lean::string_append(x_3, x_17);
lean::dec(x_17);
x_2 = x_19;
x_3 = x_20;
x_4 = x_16;
goto _start;
}
case 3:
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_4);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::cnstr_get(x_4, 0);
lean::dec(x_23);
x_24 = !lean::is_exclusive(x_5);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_5, 0);
x_26 = lean::cnstr_get(x_5, 1);
lean::dec(x_26);
x_27 = lean::cnstr_get(x_6, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_6, 1);
lean::inc(x_28);
lean::dec(x_6);
x_29 = lean::nat_add(x_25, x_27);
lean::dec(x_27);
lean::dec(x_25);
lean::cnstr_set(x_5, 1, x_28);
lean::cnstr_set(x_5, 0, x_29);
goto _start;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_32 = lean::cnstr_get(x_6, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_6, 1);
lean::inc(x_33);
lean::dec(x_6);
x_34 = lean::nat_add(x_31, x_32);
lean::dec(x_32);
lean::dec(x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_4, 0, x_35);
goto _start;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 1);
lean::inc(x_37);
lean::dec(x_4);
x_38 = lean::cnstr_get(x_5, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_39 = x_5;
} else {
 lean::dec_ref(x_5);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_6, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_6, 1);
lean::inc(x_41);
lean::dec(x_6);
x_42 = lean::nat_add(x_38, x_40);
lean::dec(x_40);
lean::dec(x_38);
if (lean::is_scalar(x_39)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_39;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
x_4 = x_44;
goto _start;
}
}
case 4:
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_4);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = lean::cnstr_get(x_4, 0);
lean::dec(x_47);
x_48 = !lean::is_exclusive(x_5);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_49 = lean::cnstr_get(x_5, 0);
x_50 = lean::cnstr_get(x_5, 1);
lean::dec(x_50);
x_51 = lean::cnstr_get(x_6, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_6, 1);
lean::inc(x_52);
lean::dec(x_6);
lean::inc(x_49);
lean::cnstr_set(x_5, 1, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_4, 0, x_53);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_5);
lean::cnstr_set(x_54, 1, x_4);
x_4 = x_54;
goto _start;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = lean::cnstr_get(x_5, 0);
lean::inc(x_56);
lean::dec(x_5);
x_57 = lean::cnstr_get(x_6, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_6, 1);
lean::inc(x_58);
lean::dec(x_6);
lean::inc(x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set(x_60, 1, x_58);
lean::cnstr_set(x_4, 0, x_60);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_4);
x_4 = x_61;
goto _start;
}
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_63 = lean::cnstr_get(x_4, 1);
lean::inc(x_63);
lean::dec(x_4);
x_64 = lean::cnstr_get(x_5, 0);
lean::inc(x_64);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_65 = x_5;
} else {
 lean::dec_ref(x_5);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_6, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_6, 1);
lean::inc(x_67);
lean::dec(x_6);
lean::inc(x_64);
if (lean::is_scalar(x_65)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_65;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_67);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_63);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
x_4 = x_71;
goto _start;
}
}
default: 
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_88; uint8 x_89; 
x_73 = lean::cnstr_get(x_4, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_74 = x_4;
} else {
 lean::dec_ref(x_4);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_76 = x_5;
} else {
 lean::dec_ref(x_5);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_6, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_6, 1);
lean::inc(x_78);
lean::dec(x_6);
x_88 = l_Lean_Format_spaceUptoLine___main(x_77, x_1);
x_89 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1 + 1);
if (x_89 == 0)
{
uint8 x_90; 
x_90 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (x_90 == 0)
{
obj* x_91; uint8 x_92; 
x_91 = l_Lean_Format_spaceUptoLine_x27___main(x_73, x_1);
x_92 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1 + 1);
if (x_92 == 0)
{
uint8 x_93; 
x_93 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; uint8 x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_88, 0);
lean::inc(x_94);
lean::dec(x_88);
x_95 = lean::cnstr_get(x_91, 0);
lean::inc(x_95);
lean::dec(x_91);
x_96 = lean::nat_add(x_94, x_95);
lean::dec(x_95);
lean::dec(x_94);
x_97 = lean::nat_dec_lt(x_1, x_96);
x_98 = 0;
x_99 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1 + 1, x_97);
x_79 = x_99;
goto block_87;
}
else
{
lean::dec(x_88);
x_79 = x_91;
goto block_87;
}
}
else
{
lean::dec(x_88);
x_79 = x_91;
goto block_87;
}
}
else
{
x_79 = x_88;
goto block_87;
}
}
else
{
x_79 = x_88;
goto block_87;
}
block_87:
{
uint8 x_80; 
x_80 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1 + 1);
lean::dec(x_79);
if (x_80 == 0)
{
obj* x_81; obj* x_82; 
lean::dec(x_78);
if (lean::is_scalar(x_76)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_76;
}
lean::cnstr_set(x_81, 0, x_75);
lean::cnstr_set(x_81, 1, x_77);
if (lean::is_scalar(x_74)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_74;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_73);
x_4 = x_82;
goto _start;
}
else
{
obj* x_84; obj* x_85; 
lean::dec(x_77);
if (lean::is_scalar(x_76)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_76;
}
lean::cnstr_set(x_84, 0, x_75);
lean::cnstr_set(x_84, 1, x_78);
if (lean::is_scalar(x_74)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_74;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_73);
x_4 = x_85;
goto _start;
}
}
}
}
}
}
}
obj* l_Lean_Format_be___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Format_be___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Format_be(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Format_be___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Format_be___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Format_be(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Format_bracket(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::string_length(x_1);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = 0;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_6);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_6);
x_10 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Format_group___main(x_10);
return x_11;
}
}
obj* _init_l_Lean_Format_paren___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("(");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_paren___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(")");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_paren___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("(");
x_2 = lean::string_length(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Format_paren(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = 0;
x_3 = l_Lean_Format_paren___closed__1;
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = l_Lean_Format_paren___closed__2;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_2);
x_7 = l_Lean_Format_paren___closed__3;
x_8 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = l_Lean_Format_group___main(x_8);
return x_9;
}
}
obj* _init_l_Lean_Format_sbracket___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("[");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_sbracket___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("]");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_sbracket___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("[");
x_2 = lean::string_length(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Format_sbracket(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = 0;
x_3 = l_Lean_Format_sbracket___closed__1;
x_4 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = l_Lean_Format_sbracket___closed__2;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_2);
x_7 = l_Lean_Format_sbracket___closed__3;
x_8 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = l_Lean_Format_group___main(x_8);
return x_9;
}
}
obj* _init_l_Lean_Format_defIndent() {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(4u);
return x_1;
}
}
uint8 _init_l_Lean_Format_defUnicode() {
_start:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
}
obj* _init_l_Lean_Format_defWidth() {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(120u);
return x_1;
}
}
obj* _init_l_Lean_Format_getWidth___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("format");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("width");
x_5 = lean_name_mk_string(x_3, x_4);
return x_5;
}
}
obj* l_Lean_Format_getWidth(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_defWidth;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_getWidth___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_getWidth(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_getIndent___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("format");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("indent");
x_5 = lean_name_mk_string(x_3, x_4);
return x_5;
}
}
obj* l_Lean_Format_getIndent(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Format_getIndent___closed__1;
x_3 = l_Lean_Format_defIndent;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_getIndent___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_getIndent(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_getUnicode___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("format");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("unicode");
x_5 = lean_name_mk_string(x_3, x_4);
return x_5;
}
}
uint8 l_Lean_Format_getUnicode(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; uint8 x_4; 
x_2 = l_Lean_Format_getUnicode___closed__1;
x_3 = l_Lean_Format_defUnicode;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_getUnicode___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Format_getUnicode(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_Format_indentOption___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Format_defIndent;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("format");
x_4 = lean::mk_string("indentation");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* l_Lean_Format_indentOption(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Format_getIndent___closed__1;
x_3 = l_Lean_Format_indentOption___closed__1;
x_4 = l_Lean_registerOption(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Format_unicodeOption___closed__1() {
_start:
{
uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Format_defUnicode;
x_2 = lean::alloc_cnstr(1, 0, 1);
lean::cnstr_set_scalar(x_2, 0, x_1);
x_3 = lean::mk_string("format");
x_4 = lean::mk_string("unicode characters");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* l_Lean_Format_unicodeOption(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Format_getUnicode___closed__1;
x_3 = l_Lean_Format_unicodeOption___closed__1;
x_4 = l_Lean_registerOption(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Format_widthOption___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Format_defWidth;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("format");
x_4 = lean::mk_string("line width");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* l_Lean_Format_widthOption(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = l_Lean_Format_widthOption___closed__1;
x_4 = l_Lean_registerOption(x_2, x_3, x_1);
return x_4;
}
}
namespace lean {
obj* format_pretty_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_Lean_Format_be___main(x_2, x_3, x_7, x_6);
lean::dec(x_2);
return x_8;
}
}
}
obj* l_Lean_Format_pretty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Format_getWidth(x_2);
x_4 = lean::format_pretty_core(x_1, x_3);
return x_4;
}
}
obj* l_Lean_Format_pretty___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_pretty(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_fmt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_Lean_fmt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_fmt___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_toStringToFormat___rarg___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_toStringToFormat___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_toStringToFormat___rarg___lambda__1), 1, 0);
return x_1;
}
}
obj* l_Lean_toStringToFormat___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_toStringToFormat___rarg___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_toStringToFormat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_toStringToFormat___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_formatHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_stringHasFormat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Format_joinSep___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = 0;
lean::inc(x_3);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = l_Lean_Format_joinSep___main___rarg(x_1, x_5, x_3);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
return x_13;
}
}
}
}
obj* l_Lean_Format_joinSep___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSep___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Format_joinSep___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Format_joinSep___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_joinSep(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSep___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Format_prefixJoin___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = 0;
lean::inc(x_2);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_8);
x_10 = l_Lean_Format_prefixJoin___main___rarg(x_1, x_2, x_6);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_8);
return x_11;
}
}
}
obj* l_Lean_Format_prefixJoin___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_prefixJoin___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Format_prefixJoin___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Format_prefixJoin___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_prefixJoin(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_prefixJoin___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Format_joinSuffix___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = 0;
lean::inc(x_3);
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_8);
x_10 = l_Lean_Format_joinSuffix___main___rarg(x_1, x_6, x_3);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_8);
return x_11;
}
}
}
obj* l_Lean_Format_joinSuffix___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSuffix___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Format_joinSuffix___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Format_joinSuffix___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Format_joinSuffix(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinSuffix___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_Lean_List_format___main___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("[]");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_List_format___main___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_string(",");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 0;
x_4 = lean::box(1);
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
obj* l_Lean_List_format___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Lean_List_format___main___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = l_Lean_List_format___main___rarg___closed__2;
x_5 = l_Lean_Format_joinSep___main___rarg(x_1, x_2, x_4);
x_6 = 0;
x_7 = l_Lean_Format_sbracket___closed__1;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = l_Lean_Format_sbracket___closed__2;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_6);
x_11 = l_Lean_Format_sbracket___closed__3;
x_12 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Format_group___main(x_12);
return x_13;
}
}
}
obj* l_Lean_List_format___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_format___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_List_format___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_List_format___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_List_format(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_format___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_listHasFormat___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_List_format___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_listHasFormat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_listHasFormat___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_prodHasFormat___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(",");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_prodHasFormat___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::apply_1(x_1, x_4);
x_7 = 0;
x_8 = l_Lean_prodHasFormat___rarg___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = lean::box(1);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_7);
x_12 = lean::apply_1(x_2, x_5);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_7);
x_14 = l_Lean_Format_paren___closed__1;
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_7);
x_16 = l_Lean_Format_paren___closed__2;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_7);
x_18 = l_Lean_Format_paren___closed__3;
x_19 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_Lean_Format_group___main(x_19);
return x_20;
}
}
obj* l_Lean_prodHasFormat(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_prodHasFormat___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_lt(x_10, x_5);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_5, x_12);
lean::dec(x_5);
if (x_11 == 0)
{
obj* x_14; uint8 x_15; obj* x_16; 
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_9);
x_15 = 0;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_15);
x_5 = x_13;
x_6 = x_16;
goto _start;
}
else
{
uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = 0;
lean::inc(x_3);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_6);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_18);
lean::inc(x_1);
x_20 = lean::apply_1(x_1, x_9);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_18);
x_5 = x_13;
x_6 = x_21;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Format_joinArraySep___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::box(0);
x_6 = l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(x_1, x_2, x_3, x_2, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Format_joinArraySep(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_joinArraySep___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Format_joinArraySep___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Format_joinArraySep___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Format_joinArraySep___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_natHasFormat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_uint16HasFormat(uint16 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::uint16_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_uint16HasFormat___boxed(obj* x_1) {
_start:
{
uint16 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_uint16HasFormat(x_2);
return x_3;
}
}
obj* l_Lean_uint32HasFormat(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::uint32_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_uint32HasFormat___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Lean_uint32HasFormat(x_2);
return x_3;
}
}
obj* l_Lean_uint64HasFormat(uint64 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::uint64_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_uint64HasFormat___boxed(obj* x_1) {
_start:
{
uint64 x_2; obj* x_3; 
x_2 = lean::unbox_uint64(x_1);
lean::dec(x_1);
x_3 = l_Lean_uint64HasFormat(x_2);
return x_3;
}
}
obj* l_Lean_usizeHasFormat(usize x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::usize_to_nat(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_usizeHasFormat___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_3 = l_Lean_usizeHasFormat(x_2);
return x_3;
}
}
obj* l_Lean_nameHasFormat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_Lean_Format_repr___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("Format.nil");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_repr___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("Format.line");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Format_repr___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_string("Format.text");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 0;
x_4 = lean::box(1);
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
obj* _init_l_Lean_Format_repr___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_string("Format.nest");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 0;
x_4 = lean::box(1);
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
obj* _init_l_Lean_Format_repr___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string("Format.compose ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("false");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_5);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_5);
return x_8;
}
}
obj* _init_l_Lean_Format_repr___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string("Format.compose ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("true");
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_5);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_5);
return x_8;
}
}
obj* _init_l_Lean_Format_repr___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_string("Format.choice");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 0;
x_4 = lean::box(1);
x_5 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
obj* l_Lean_Format_repr___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Format_repr___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; 
x_3 = l_Lean_Format_repr___main___closed__2;
return x_3;
}
case 2:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = l_String_quote(x_5);
lean::cnstr_set(x_1, 0, x_6);
x_7 = 0;
x_8 = l_Lean_Format_repr___main___closed__3;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = l_Lean_Format_paren___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_7);
x_12 = l_Lean_Format_paren___closed__2;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_7);
x_14 = l_Lean_Format_paren___closed__3;
x_15 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_Lean_Format_group___main(x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_18 = l_String_quote(x_17);
x_19 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = 0;
x_21 = l_Lean_Format_repr___main___closed__3;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_20);
x_23 = l_Lean_Format_paren___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_20);
x_25 = l_Lean_Format_paren___closed__2;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_20);
x_27 = l_Lean_Format_paren___closed__3;
x_28 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = l_Lean_Format_group___main(x_28);
return x_29;
}
}
case 3:
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_1);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_31 = lean::cnstr_get(x_1, 0);
x_32 = lean::cnstr_get(x_1, 1);
x_33 = l_Nat_repr(x_31);
x_34 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = 0;
x_36 = l_Lean_Format_repr___main___closed__4;
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_35);
x_38 = lean::box(1);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_35);
x_40 = l_Lean_Format_repr___main(x_32);
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_35);
x_42 = l_Lean_Format_paren___closed__1;
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_35);
x_44 = l_Lean_Format_paren___closed__2;
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_35);
x_46 = l_Lean_Format_paren___closed__3;
lean::cnstr_set(x_1, 1, x_45);
lean::cnstr_set(x_1, 0, x_46);
x_47 = l_Lean_Format_group___main(x_1);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_48 = lean::cnstr_get(x_1, 0);
x_49 = lean::cnstr_get(x_1, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_1);
x_50 = l_Nat_repr(x_48);
x_51 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = 0;
x_53 = l_Lean_Format_repr___main___closed__4;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_52);
x_55 = lean::box(1);
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_52);
x_57 = l_Lean_Format_repr___main(x_49);
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_52);
x_59 = l_Lean_Format_paren___closed__1;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_58);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_52);
x_61 = l_Lean_Format_paren___closed__2;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_52);
x_63 = l_Lean_Format_paren___closed__3;
x_64 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_Lean_Format_group___main(x_64);
return x_65;
}
}
case 4:
{
uint8 x_66; 
x_66 = !lean::is_exclusive(x_1);
if (x_66 == 0)
{
uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
x_68 = lean::cnstr_get(x_1, 0);
x_69 = lean::cnstr_get(x_1, 1);
x_70 = l_Lean_Format_repr___main(x_68);
x_71 = l_Lean_Format_repr___main(x_69);
if (x_67 == 0)
{
uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_72 = 0;
x_73 = l_Lean_Format_repr___main___closed__5;
lean::cnstr_set(x_1, 1, x_70);
lean::cnstr_set(x_1, 0, x_73);
lean::cnstr_set_scalar(x_1, sizeof(void*)*2, x_72);
x_74 = lean::box(1);
x_75 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_75, 0, x_1);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set_scalar(x_75, sizeof(void*)*2, x_72);
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_71);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_72);
x_77 = l_Lean_Format_paren___closed__1;
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_72);
x_79 = l_Lean_Format_paren___closed__2;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_72);
x_81 = l_Lean_Format_paren___closed__3;
x_82 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = l_Lean_Format_group___main(x_82);
return x_83;
}
else
{
uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_84 = 0;
x_85 = l_Lean_Format_repr___main___closed__6;
lean::cnstr_set(x_1, 1, x_70);
lean::cnstr_set(x_1, 0, x_85);
lean::cnstr_set_scalar(x_1, sizeof(void*)*2, x_84);
x_86 = lean::box(1);
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_1);
lean::cnstr_set(x_87, 1, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_84);
x_88 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_71);
lean::cnstr_set_scalar(x_88, sizeof(void*)*2, x_84);
x_89 = l_Lean_Format_paren___closed__1;
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_84);
x_91 = l_Lean_Format_paren___closed__2;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_84);
x_93 = l_Lean_Format_paren___closed__3;
x_94 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_92);
x_95 = l_Lean_Format_group___main(x_94);
return x_95;
}
}
else
{
uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_96 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
x_97 = lean::cnstr_get(x_1, 0);
x_98 = lean::cnstr_get(x_1, 1);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_1);
x_99 = l_Lean_Format_repr___main(x_97);
x_100 = l_Lean_Format_repr___main(x_98);
if (x_96 == 0)
{
uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_101 = 0;
x_102 = l_Lean_Format_repr___main___closed__5;
x_103 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
lean::cnstr_set_scalar(x_103, sizeof(void*)*2, x_101);
x_104 = lean::box(1);
x_105 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*2, x_101);
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_100);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_101);
x_107 = l_Lean_Format_paren___closed__1;
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_106);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_101);
x_109 = l_Lean_Format_paren___closed__2;
x_110 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set(x_110, 1, x_109);
lean::cnstr_set_scalar(x_110, sizeof(void*)*2, x_101);
x_111 = l_Lean_Format_paren___closed__3;
x_112 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_110);
x_113 = l_Lean_Format_group___main(x_112);
return x_113;
}
else
{
uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_114 = 0;
x_115 = l_Lean_Format_repr___main___closed__6;
x_116 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_99);
lean::cnstr_set_scalar(x_116, sizeof(void*)*2, x_114);
x_117 = lean::box(1);
x_118 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_117);
lean::cnstr_set_scalar(x_118, sizeof(void*)*2, x_114);
x_119 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set_scalar(x_119, sizeof(void*)*2, x_114);
x_120 = l_Lean_Format_paren___closed__1;
x_121 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_119);
lean::cnstr_set_scalar(x_121, sizeof(void*)*2, x_114);
x_122 = l_Lean_Format_paren___closed__2;
x_123 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*2, x_114);
x_124 = l_Lean_Format_paren___closed__3;
x_125 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_123);
x_126 = l_Lean_Format_group___main(x_125);
return x_126;
}
}
}
default: 
{
uint8 x_127; 
x_127 = !lean::is_exclusive(x_1);
if (x_127 == 0)
{
obj* x_128; obj* x_129; obj* x_130; uint8 x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_128 = lean::cnstr_get(x_1, 0);
x_129 = lean::cnstr_get(x_1, 1);
x_130 = l_Lean_Format_repr___main(x_128);
x_131 = 0;
x_132 = l_Lean_Format_repr___main___closed__7;
x_133 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_130);
lean::cnstr_set_scalar(x_133, sizeof(void*)*2, x_131);
x_134 = lean::box(1);
x_135 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*2, x_131);
x_136 = l_Lean_Format_repr___main(x_129);
x_137 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_137, 0, x_135);
lean::cnstr_set(x_137, 1, x_136);
lean::cnstr_set_scalar(x_137, sizeof(void*)*2, x_131);
x_138 = l_Lean_Format_paren___closed__1;
x_139 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_137);
lean::cnstr_set_scalar(x_139, sizeof(void*)*2, x_131);
x_140 = l_Lean_Format_paren___closed__2;
x_141 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_141, 0, x_139);
lean::cnstr_set(x_141, 1, x_140);
lean::cnstr_set_scalar(x_141, sizeof(void*)*2, x_131);
x_142 = l_Lean_Format_paren___closed__3;
lean::cnstr_set_tag(x_1, 3);
lean::cnstr_set(x_1, 1, x_141);
lean::cnstr_set(x_1, 0, x_142);
x_143 = l_Lean_Format_group___main(x_1);
return x_143;
}
else
{
obj* x_144; obj* x_145; obj* x_146; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_144 = lean::cnstr_get(x_1, 0);
x_145 = lean::cnstr_get(x_1, 1);
lean::inc(x_145);
lean::inc(x_144);
lean::dec(x_1);
x_146 = l_Lean_Format_repr___main(x_144);
x_147 = 0;
x_148 = l_Lean_Format_repr___main___closed__7;
x_149 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_146);
lean::cnstr_set_scalar(x_149, sizeof(void*)*2, x_147);
x_150 = lean::box(1);
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_147);
x_152 = l_Lean_Format_repr___main(x_145);
x_153 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_153, 0, x_151);
lean::cnstr_set(x_153, 1, x_152);
lean::cnstr_set_scalar(x_153, sizeof(void*)*2, x_147);
x_154 = l_Lean_Format_paren___closed__1;
x_155 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_153);
lean::cnstr_set_scalar(x_155, sizeof(void*)*2, x_147);
x_156 = l_Lean_Format_paren___closed__2;
x_157 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_157, 0, x_155);
lean::cnstr_set(x_157, 1, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*2, x_147);
x_158 = l_Lean_Format_paren___closed__3;
x_159 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_157);
x_160 = l_Lean_Format_group___main(x_159);
return x_160;
}
}
}
}
}
obj* l_Lean_Format_repr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_repr___main(x_1);
return x_2;
}
}
obj* l_Lean_formatHasToString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
}
}
obj* l_Lean_HasRepr___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_HasRepr() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_HasRepr___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Format_repr), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_formatDataValue___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("false");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_formatDataValue___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("true");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_formatDataValue___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("`");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_formatDataValue___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_String_quote(x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_1, 0);
lean::dec(x_1);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_Lean_formatDataValue___main___closed__1;
return x_6;
}
else
{
obj* x_7; 
x_7 = l_Lean_formatDataValue___main___closed__2;
return x_7;
}
}
case 2:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_8);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = 0;
x_13 = l_Lean_formatDataValue___main___closed__3;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
return x_14;
}
case 3:
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_16 = l_Nat_repr(x_15);
x_17 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
default: 
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_19 = l_Int_repr___main(x_18);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
}
obj* l_Lean_formatDataValue(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_formatDataValue___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_dataValueHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_formatDataValue), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_formatEntry___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" := ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_formatEntry___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Name_toString___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_formatEntry___main___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = l_Lean_formatDataValue___main(x_3);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_7);
return x_11;
}
}
obj* l_Lean_formatEntry(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_formatEntry___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_entryHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_formatEntry), 1, 0);
return x_1;
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_formatEntry___main(x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = l_Lean_formatEntry___main(x_7);
x_9 = 0;
lean::inc(x_2);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_2);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(x_4, x_2);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_9);
return x_12;
}
}
}
}
obj* _init_l_Lean_formatKVMap___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(", ");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_formatKVMap(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = l_Lean_formatKVMap___closed__1;
x_3 = l_Lean_Format_joinSep___main___at_Lean_formatKVMap___spec__1(x_1, x_2);
x_4 = 0;
x_5 = l_Lean_Format_sbracket___closed__1;
x_6 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_4);
x_7 = l_Lean_Format_sbracket___closed__2;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_4);
x_9 = l_Lean_Format_sbracket___closed__3;
x_10 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Format_group___main(x_10);
return x_11;
}
}
obj* _init_l_Lean_kvMapHasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_formatKVMap), 1, 0);
return x_1;
}
}
obj* initialize_init_lean_options(obj*);
obj* initialize_init_data_array_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_format(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_options(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "append"), 2, lean::format_append_core);
l_Lean_Format_HasAppend = _init_l_Lean_Format_HasAppend();
lean::mark_persistent(l_Lean_Format_HasAppend);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "HasAppend"), l_Lean_Format_HasAppend);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "HasCoe"), 1, l_Lean_Format_HasCoe);
l_Lean_Format_Inhabited = _init_l_Lean_Format_Inhabited();
lean::mark_persistent(l_Lean_Format_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "Inhabited"), l_Lean_Format_Inhabited);
l_Lean_Format_join___closed__1 = _init_l_Lean_Format_join___closed__1();
lean::mark_persistent(l_Lean_Format_join___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "join"), 1, l_Lean_Format_join___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "isNil"), 1, l_Lean_Format_isNil___boxed);
l_Lean_Format_flatten___main___closed__1 = _init_l_Lean_Format_flatten___main___closed__1();
lean::mark_persistent(l_Lean_Format_flatten___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "flatten"), 1, l_Lean_Format_flatten);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "group"), 1, lean::format_group_core);
l_Lean_Format_spaceUptoLine___main___closed__1 = _init_l_Lean_Format_spaceUptoLine___main___closed__1();
lean::mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__1);
l_Lean_Format_spaceUptoLine___main___closed__2 = _init_l_Lean_Format_spaceUptoLine___main___closed__2();
lean::mark_persistent(l_Lean_Format_spaceUptoLine___main___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "spaceUptoLine"), 2, l_Lean_Format_spaceUptoLine___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "spaceUptoLine'"), 2, l_Lean_Format_spaceUptoLine_x27___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "be"), 4, l_Lean_Format_be___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "bracket"), 3, l_Lean_Format_bracket);
l_Lean_Format_paren___closed__1 = _init_l_Lean_Format_paren___closed__1();
lean::mark_persistent(l_Lean_Format_paren___closed__1);
l_Lean_Format_paren___closed__2 = _init_l_Lean_Format_paren___closed__2();
lean::mark_persistent(l_Lean_Format_paren___closed__2);
l_Lean_Format_paren___closed__3 = _init_l_Lean_Format_paren___closed__3();
lean::mark_persistent(l_Lean_Format_paren___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "paren"), 1, l_Lean_Format_paren);
l_Lean_Format_sbracket___closed__1 = _init_l_Lean_Format_sbracket___closed__1();
lean::mark_persistent(l_Lean_Format_sbracket___closed__1);
l_Lean_Format_sbracket___closed__2 = _init_l_Lean_Format_sbracket___closed__2();
lean::mark_persistent(l_Lean_Format_sbracket___closed__2);
l_Lean_Format_sbracket___closed__3 = _init_l_Lean_Format_sbracket___closed__3();
lean::mark_persistent(l_Lean_Format_sbracket___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "sbracket"), 1, l_Lean_Format_sbracket);
l_Lean_Format_defIndent = _init_l_Lean_Format_defIndent();
lean::mark_persistent(l_Lean_Format_defIndent);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "defIndent"), l_Lean_Format_defIndent);
l_Lean_Format_defUnicode = _init_l_Lean_Format_defUnicode();
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "defUnicode"), lean::box(l_Lean_Format_defUnicode));
l_Lean_Format_defWidth = _init_l_Lean_Format_defWidth();
lean::mark_persistent(l_Lean_Format_defWidth);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "defWidth"), l_Lean_Format_defWidth);
l_Lean_Format_getWidth___closed__1 = _init_l_Lean_Format_getWidth___closed__1();
lean::mark_persistent(l_Lean_Format_getWidth___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "getWidth"), 1, l_Lean_Format_getWidth___boxed);
l_Lean_Format_getIndent___closed__1 = _init_l_Lean_Format_getIndent___closed__1();
lean::mark_persistent(l_Lean_Format_getIndent___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "getIndent"), 1, l_Lean_Format_getIndent___boxed);
l_Lean_Format_getUnicode___closed__1 = _init_l_Lean_Format_getUnicode___closed__1();
lean::mark_persistent(l_Lean_Format_getUnicode___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "getUnicode"), 1, l_Lean_Format_getUnicode___boxed);
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "prettyAux"), 2, lean::format_pretty_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "pretty"), 2, l_Lean_Format_pretty___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "fmt"), 1, l_Lean_fmt);
l_Lean_toStringToFormat___rarg___closed__1 = _init_l_Lean_toStringToFormat___rarg___closed__1();
lean::mark_persistent(l_Lean_toStringToFormat___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "toStringToFormat"), 1, l_Lean_toStringToFormat);
l_Lean_formatHasFormat = _init_l_Lean_formatHasFormat();
lean::mark_persistent(l_Lean_formatHasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "formatHasFormat"), l_Lean_formatHasFormat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "stringHasFormat"), 1, l_Lean_stringHasFormat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "joinSep"), 1, l_Lean_Format_joinSep);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "prefixJoin"), 1, l_Lean_Format_prefixJoin);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "joinSuffix"), 1, l_Lean_Format_joinSuffix);
l_Lean_List_format___main___rarg___closed__1 = _init_l_Lean_List_format___main___rarg___closed__1();
lean::mark_persistent(l_Lean_List_format___main___rarg___closed__1);
l_Lean_List_format___main___rarg___closed__2 = _init_l_Lean_List_format___main___rarg___closed__2();
lean::mark_persistent(l_Lean_List_format___main___rarg___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "List"), "format"), 1, l_Lean_List_format);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "listHasFormat"), 1, l_Lean_listHasFormat);
l_Lean_prodHasFormat___rarg___closed__1 = _init_l_Lean_prodHasFormat___rarg___closed__1();
lean::mark_persistent(l_Lean_prodHasFormat___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "prodHasFormat"), 2, l_Lean_prodHasFormat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "joinArraySep"), 1, l_Lean_Format_joinArraySep);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "natHasFormat"), 1, l_Lean_natHasFormat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "uint16HasFormat"), 1, l_Lean_uint16HasFormat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "uint32HasFormat"), 1, l_Lean_uint32HasFormat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "uint64HasFormat"), 1, l_Lean_uint64HasFormat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "usizeHasFormat"), 1, l_Lean_usizeHasFormat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "nameHasFormat"), 1, l_Lean_nameHasFormat);
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Format"), "repr"), 1, l_Lean_Format_repr);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "formatHasToString"), 1, l_Lean_formatHasToString);
l_Lean_HasRepr = _init_l_Lean_HasRepr();
lean::mark_persistent(l_Lean_HasRepr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "HasRepr"), l_Lean_HasRepr);
l_Lean_formatDataValue___main___closed__1 = _init_l_Lean_formatDataValue___main___closed__1();
lean::mark_persistent(l_Lean_formatDataValue___main___closed__1);
l_Lean_formatDataValue___main___closed__2 = _init_l_Lean_formatDataValue___main___closed__2();
lean::mark_persistent(l_Lean_formatDataValue___main___closed__2);
l_Lean_formatDataValue___main___closed__3 = _init_l_Lean_formatDataValue___main___closed__3();
lean::mark_persistent(l_Lean_formatDataValue___main___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "formatDataValue"), 1, l_Lean_formatDataValue);
l_Lean_dataValueHasFormat = _init_l_Lean_dataValueHasFormat();
lean::mark_persistent(l_Lean_dataValueHasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "dataValueHasFormat"), l_Lean_dataValueHasFormat);
l_Lean_formatEntry___main___closed__1 = _init_l_Lean_formatEntry___main___closed__1();
lean::mark_persistent(l_Lean_formatEntry___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "formatEntry"), 1, l_Lean_formatEntry);
l_Lean_entryHasFormat = _init_l_Lean_entryHasFormat();
lean::mark_persistent(l_Lean_entryHasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "entryHasFormat"), l_Lean_entryHasFormat);
l_Lean_formatKVMap___closed__1 = _init_l_Lean_formatKVMap___closed__1();
lean::mark_persistent(l_Lean_formatKVMap___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "formatKVMap"), 1, l_Lean_formatKVMap);
l_Lean_kvMapHasFormat = _init_l_Lean_kvMapHasFormat();
lean::mark_persistent(l_Lean_kvMapHasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "kvMapHasFormat"), l_Lean_kvMapHasFormat);
return w;
}
