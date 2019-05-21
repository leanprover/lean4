// Lean compiler output
// Module: init.lean.extern
// Imports: init.lean.expr init.data.option.basic init.lean.environment
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
uint32 l_String_Iterator_curr___main(obj*);
obj* l_Lean_getExternEntryForAux___boxed(obj*, obj*);
namespace lean {
obj* mk_extern_attr_data_core(obj*, obj*);
}
obj* l_Lean_expandExternPatternAux(obj*, obj*, obj*, obj*);
extern obj* l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
obj* l_Lean_getExternNameFor(obj*, obj*, obj*);
obj* l_Lean_getExternNameFor___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_ExternEntry_backend(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
namespace lean {
obj* mk_adhoc_ext_entry_core(obj*);
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj*, obj*);
}
obj* l_List_intersperse___main___rarg(obj*, obj*);
obj* l_Lean_expandExternEntry(obj*, obj*);
obj* l_List_getOpt___main___rarg(obj*, obj*);
obj* l_Lean_getExternEntryForAux___main___closed__1;
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(obj*, obj*);
obj* l_Lean_ExternEntry_backend___main___boxed(obj*);
obj* l_Lean_expandExternEntry___main(obj*, obj*);
namespace lean {
obj* mk_extern_call_core(obj*, obj*, obj*);
}
obj* l_String_Iterator_remainingBytes___main(obj*);
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_ExternEntry_backend___boxed(obj*);
namespace lean {
obj* expand_extern_pattern_core(obj*, obj*);
}
obj* l_String_Iterator_next___main(obj*);
extern "C" obj* lean_get_extern_attr_data(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern obj* l_List_reprAux___main___rarg___closed__1;
extern obj* l_Option_HasRepr___rarg___closed__3;
uint8 l_Lean_isExternC(obj*, obj*);
obj* l_Lean_expandExternPatternAux___main(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
extern obj* l_Prod_HasRepr___rarg___closed__1;
namespace lean {
obj* mk_inline_ext_entry_core(obj*, obj*);
}
obj* l___private_init_lean_extern_1__parseOptNum(obj*, obj*, obj*);
obj* l_Lean_getExternAttrData___boxed(obj*, obj*);
obj* l_Lean_getExternEntryForAux(obj*, obj*);
obj* l_Lean_getExternEntryForAux___main___boxed(obj*, obj*);
obj* l___private_init_lean_extern_1__parseOptNum___main(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
uint8 l_String_Iterator_hasNext___main(obj*);
obj* l_Lean_getExternEntryForAux___main(obj*, obj*);
namespace lean {
obj* get_extern_entry_for_core(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
namespace lean {
obj* mk_std_ext_entry_core(obj*, obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_ExternEntry_backend___main(obj*);
obj* l_Lean_isExternC___boxed(obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_mkSimpleFnCall(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
namespace lean {
obj* mk_adhoc_ext_entry_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
}
namespace lean {
obj* mk_inline_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_std_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_extern_attr_data_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
obj* l___private_init_lean_extern_1__parseOptNum___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_8; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
x_8 = l_String_Iterator_hasNext___main(x_1);
if (x_8 == 0)
{
obj* x_10; 
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_2);
return x_10;
}
else
{
uint32 x_11; uint32 x_12; uint8 x_13; 
x_11 = l_String_Iterator_curr___main(x_1);
x_12 = 48;
x_13 = x_12 <= x_11;
if (x_13 == 0)
{
obj* x_15; 
lean::dec(x_6);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_2);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = 57;
x_17 = x_11 <= x_16;
if (x_17 == 0)
{
obj* x_19; 
lean::dec(x_6);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_20 = l_String_Iterator_next___main(x_1);
x_21 = lean::mk_nat_obj(10ul);
x_22 = lean::nat_mul(x_2, x_21);
lean::dec(x_2);
x_24 = lean::uint32_to_nat(x_11);
x_25 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_26 = lean::nat_sub(x_24, x_25);
lean::dec(x_24);
x_28 = lean::nat_add(x_22, x_26);
lean::dec(x_26);
lean::dec(x_22);
x_0 = x_6;
x_1 = x_20;
x_2 = x_28;
goto _start;
}
}
}
}
else
{
obj* x_33; 
lean::dec(x_0);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_2);
return x_33;
}
}
}
obj* l___private_init_lean_extern_1__parseOptNum(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_extern_1__parseOptNum___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_expandExternPatternAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_9; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_9 = l_String_Iterator_hasNext___main(x_2);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
uint32 x_13; uint32 x_14; uint8 x_15; 
x_13 = l_String_Iterator_curr___main(x_2);
x_14 = 35;
x_15 = x_13 == x_14;
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_String_Iterator_next___main(x_2);
x_17 = lean::string_push(x_3, x_13);
x_1 = x_7;
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_30; 
x_19 = l_String_Iterator_next___main(x_2);
x_20 = l_String_Iterator_remainingBytes___main(x_19);
x_21 = l___private_init_lean_extern_1__parseOptNum___main(x_20, x_19, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::nat_sub(x_24, x_6);
lean::dec(x_24);
lean::inc(x_0);
x_30 = l_List_getOpt___main___rarg(x_27, x_0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_String_splitAux___main___closed__1;
x_32 = lean::string_append(x_3, x_31);
x_1 = x_7;
x_2 = x_22;
x_3 = x_32;
goto _start;
}
else
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
x_37 = lean::string_append(x_3, x_34);
lean::dec(x_34);
x_1 = x_7;
x_2 = x_22;
x_3 = x_37;
goto _start;
}
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Lean_expandExternPatternAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_expandExternPatternAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
namespace lean {
obj* expand_extern_pattern_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_length(x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_String_splitAux___main___closed__1;
x_6 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_4, x_5);
return x_6;
}
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_append(x_0, x_2);
x_0 = x_4;
x_1 = x_3;
goto _start;
}
}
}
obj* l_Lean_mkSimpleFnCall(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
x_2 = l_Prod_HasRepr___rarg___closed__1;
x_3 = lean::string_append(x_0, x_2);
x_4 = l_List_reprAux___main___rarg___closed__1;
x_5 = l_List_intersperse___main___rarg(x_4, x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_6, x_5);
lean::dec(x_5);
x_9 = lean::string_append(x_3, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_expandExternEntry___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::expand_extern_pattern_core(x_5, x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
default:
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_Lean_mkSimpleFnCall(x_10, x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
}
obj* l_Lean_expandExternEntry(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_expandExternEntry___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_ExternEntry_backend___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_ExternEntry_backend___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_ExternEntry_backend(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_ExternEntry_backend___main(x_0);
return x_1;
}
}
obj* l_Lean_ExternEntry_backend___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_ExternEntry_backend(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_getExternEntryForAux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("all");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_getExternEntryForAux___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_Lean_ExternEntry_backend___main(x_3);
x_9 = l_Lean_getExternEntryForAux___main___closed__1;
x_10 = lean_name_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = lean_name_dec_eq(x_8, x_0);
lean::dec(x_8);
if (x_11 == 0)
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_3);
return x_16;
}
}
else
{
obj* x_19; 
lean::dec(x_8);
lean::dec(x_5);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_3);
return x_19;
}
}
}
}
obj* l_Lean_getExternEntryForAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getExternEntryForAux___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_getExternEntryForAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getExternEntryForAux___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_getExternEntryForAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getExternEntryForAux(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
namespace lean {
obj* get_extern_entry_for_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_getExternEntryForAux___main(x_1, x_2);
lean::dec(x_1);
return x_5;
}
}
}
namespace lean {
obj* mk_extern_call_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::get_extern_entry_for_core(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_Lean_expandExternEntry___main(x_6, x_2);
return x_9;
}
}
}
}
obj* l_Lean_getExternAttrData___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_get_extern_attr_data(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_isExternC(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_get_extern_attr_data(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
switch (lean::obj_tag(x_11)) {
case 2:
{
obj* x_13; obj* x_16; obj* x_19; uint8 x_20; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = l_Lean_getExternEntryForAux___main___closed__1;
x_20 = lean_name_dec_eq(x_16, x_19);
lean::dec(x_16);
if (x_20 == 0)
{
uint8 x_23; 
lean::dec(x_13);
x_23 = 0;
return x_23;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
uint8 x_24; 
x_24 = 1;
return x_24;
}
else
{
uint8 x_26; 
lean::dec(x_13);
x_26 = 0;
return x_26;
}
}
}
default:
{
uint8 x_29; 
lean::dec(x_11);
lean::dec(x_7);
x_29 = 0;
return x_29;
}
}
}
}
}
}
obj* l_Lean_isExternC___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_isExternC(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getExternNameFor(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::get_extern_entry_for_core(x_6, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_13 = x_9;
} else {
 lean::inc(x_11);
 lean::dec(x_9);
 x_13 = lean::box(0);
}
switch (lean::obj_tag(x_11)) {
case 2:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
case 3:
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
lean::dec(x_11);
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
default:
{
obj* x_24; 
lean::dec(x_11);
lean::dec(x_13);
x_24 = lean::box(0);
return x_24;
}
}
}
}
}
}
obj* l_Lean_getExternNameFor___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternNameFor(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_lean_expr(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_extern(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
 l_Lean_getExternEntryForAux___main___closed__1 = _init_l_Lean_getExternEntryForAux___main___closed__1();
lean::mark_persistent(l_Lean_getExternEntryForAux___main___closed__1);
return w;
}
