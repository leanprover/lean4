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
obj* l_Lean_isExtern___boxed(obj*, obj*);
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_ExternEntry_backend___boxed(obj*);
obj* l_Lean_expandExternPatternAux___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* expand_extern_pattern_core(obj*, obj*);
}
obj* l_String_Iterator_next___main(obj*);
extern "C" obj* lean_get_extern_attr_data(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
uint8 l_UInt32_decLe(uint32, uint32);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_Lean_expandExternPatternAux___main___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
uint8 l_Lean_isExtern(obj*, obj*);
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
uint8 l_UInt32_decEq(uint32, uint32);
namespace lean {
obj* mk_inline_ext_entry_core(obj*, obj*);
}
obj* l___private_init_lean_extern_1__parseOptNum(obj*, obj*, obj*);
obj* l_Lean_getExternAttrData___boxed(obj*, obj*);
obj* l_Lean_getExternEntryForAux(obj*, obj*);
obj* l_Lean_getExternEntryForAux___main___boxed(obj*, obj*);
obj* l___private_init_lean_extern_1__parseOptNum___main(obj*, obj*, obj*);
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
obj* mk_adhoc_ext_entry_core(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_inline_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
namespace lean {
obj* mk_std_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
namespace lean {
obj* mk_extern_attr_data_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
obj* l___private_init_lean_extern_1__parseOptNum___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_Iterator_hasNext___main(x_2);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = 48;
x_12 = x_11 <= x_10;
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 57;
x_15 = x_10 <= x_14;
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_7);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = l_String_Iterator_next___main(x_2);
x_18 = lean::mk_nat_obj(10u);
x_19 = lean::nat_mul(x_3, x_18);
lean::dec(x_3);
x_20 = lean::uint32_to_nat(x_10);
x_21 = lean::mk_nat_obj(48u);
x_22 = lean::nat_sub(x_20, x_21);
lean::dec(x_20);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_22);
lean::dec(x_19);
x_1 = x_7;
x_2 = x_17;
x_3 = x_23;
goto _start;
}
}
}
}
else
{
obj* x_25; 
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_3);
return x_25;
}
}
}
obj* l___private_init_lean_extern_1__parseOptNum(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_extern_1__parseOptNum___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_expandExternPatternAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = l_String_Iterator_hasNext___main(x_3);
if (x_9 == 0)
{
lean::dec(x_8);
lean::dec(x_3);
return x_4;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = 35;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_String_Iterator_next___main(x_3);
x_14 = lean::string_push(x_4, x_10);
x_2 = x_8;
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = l_String_Iterator_next___main(x_3);
x_17 = l_String_Iterator_remainingBytes___main(x_16);
x_18 = l___private_init_lean_extern_1__parseOptNum___main(x_17, x_16, x_5);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
x_21 = lean::nat_sub(x_20, x_7);
lean::dec(x_20);
x_22 = l_List_getOpt___main___rarg(x_21, x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
x_23 = l_String_splitAux___main___closed__1;
x_24 = lean::string_append(x_4, x_23);
x_2 = x_8;
x_3 = x_19;
x_4 = x_24;
goto _start;
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_27 = lean::string_append(x_4, x_26);
lean::dec(x_26);
x_2 = x_8;
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Lean_expandExternPatternAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_expandExternPatternAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_expandExternPatternAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
namespace lean {
obj* expand_extern_pattern_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::string_length(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_Lean_expandExternPatternAux___main(x_2, x_3, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* l_Lean_mkSimpleFnCall(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = l_Prod_HasRepr___rarg___closed__1;
x_4 = lean::string_append(x_1, x_3);
x_5 = l_List_reprAux___main___rarg___closed__1;
x_6 = l_List_intersperse___main___rarg(x_5, x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_7, x_6);
lean::dec(x_6);
x_9 = lean::string_append(x_4, x_8);
lean::dec(x_8);
x_10 = l_Option_HasRepr___rarg___closed__3;
x_11 = lean::string_append(x_9, x_10);
return x_11;
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_expandExternEntry___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::expand_extern_pattern_core(x_4, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
default: 
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = l_Lean_mkSimpleFnCall(x_7, x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_Lean_expandExternEntry(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_expandExternEntry___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_ExternEntry_backend___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend___main(x_1);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_getExternEntryForAux___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("all");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_getExternEntryForAux___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_ExternEntry_backend___main(x_4);
x_7 = l_Lean_getExternEntryForAux___main___closed__1;
x_8 = lean_name_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean_name_dec_eq(x_6, x_1);
lean::dec(x_6);
if (x_9 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
obj* x_11; 
lean::inc(x_4);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_4);
return x_11;
}
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::inc(x_4);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_4);
return x_12;
}
}
}
}
obj* l_Lean_getExternEntryForAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getExternEntryForAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_getExternEntryForAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
namespace lean {
obj* get_extern_entry_for_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_getExternEntryForAux___main(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
namespace lean {
obj* mk_extern_call_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::get_extern_entry_for_core(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_expandExternEntry___main(x_6, x_3);
return x_7;
}
}
}
}
obj* l_Lean_getExternAttrData___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
return x_3;
}
}
uint8 l_Lean_isExtern(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_3);
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_isExtern___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isExternC(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 2)
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = l_Lean_getExternEntryForAux___main___closed__1;
x_12 = lean_name_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_9);
x_13 = 0;
return x_13;
}
else
{
if (lean::obj_tag(x_9) == 0)
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8 x_15; 
lean::dec(x_9);
x_15 = 0;
return x_15;
}
}
}
else
{
uint8 x_16; 
lean::dec(x_8);
lean::dec(x_6);
x_16 = 0;
return x_16;
}
}
}
}
}
obj* l_Lean_isExternC___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_getExternNameFor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_get_extern_attr_data(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::get_extern_entry_for_core(x_6, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_7, 0);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; 
lean::free_heap_obj(x_7);
lean::dec(x_10);
x_11 = lean::box(0);
return x_11;
}
case 1:
{
obj* x_12; 
lean::free_heap_obj(x_7);
lean::dec(x_10);
x_12 = lean::box(0);
return x_12;
}
default: 
{
obj* x_13; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
lean::cnstr_set(x_7, 0, x_13);
return x_7;
}
}
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_15; 
lean::dec(x_14);
x_15 = lean::box(0);
return x_15;
}
case 1:
{
obj* x_16; 
lean::dec(x_14);
x_16 = lean::box(0);
return x_16;
}
default: 
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
}
}
obj* l_Lean_getExternNameFor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkAdhocExtEntry"), 1, lean::mk_adhoc_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkInlineExtEntry"), 2, lean::mk_inline_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkStdExtEntry"), 2, lean::mk_std_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkForeignExtEntry"), 2, lean::mk_foreign_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkExternAttrData"), 2, lean::mk_extern_attr_data_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternPatternAux"), 4, l_Lean_expandExternPatternAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternPattern"), 2, lean::expand_extern_pattern_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkSimpleFnCall"), 2, l_Lean_mkSimpleFnCall);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternEntry"), 2, l_Lean_expandExternEntry);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ExternEntry"), "backend"), 1, l_Lean_ExternEntry_backend___boxed);
l_Lean_getExternEntryForAux___main___closed__1 = _init_l_Lean_getExternEntryForAux___main___closed__1();
lean::mark_persistent(l_Lean_getExternEntryForAux___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternEntryForAux"), 2, l_Lean_getExternEntryForAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternEntryFor"), 2, lean::get_extern_entry_for_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkExternCall"), 3, lean::mk_extern_call_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternAttrData"), 2, l_Lean_getExternAttrData___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isExtern"), 2, l_Lean_isExtern___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isExternC"), 2, l_Lean_isExternC___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternNameFor"), 3, l_Lean_getExternNameFor___boxed);
return w;
}
