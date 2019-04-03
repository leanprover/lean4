// Lean compiler output
// Module: init.lean.name
// Imports: init.data.string.basic init.coe init.data.uint init.data.tostring init.data.hashable init.data.rbmap.default init.data.rbtree.default
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
obj* l_Lean_NameMap_contains___rarg___closed__1;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Name_HasToString;
obj* l_Lean_Name_toStringWithSep___main___closed__1;
obj* l_Lean_NameMap_insert(obj*);
obj* l_Lean_Name_Hashable;
obj* l_Lean_stringToName;
obj* l_Lean_Name_hasLtQuick;
obj* l_Lean_Name_quickLtCore___boxed(obj*, obj*);
obj* l_Lean_Name_replacePrefix___boxed(obj*, obj*, obj*);
obj* l_Lean_NameMap_contains___boxed(obj*);
obj* l_Lean_NameMap_HasEmptyc(obj*);
obj* l_Lean_Name_components(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Name_updatePrefix(obj*, obj*);
obj* l_Lean_Name_hash___boxed(obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_Inhabited;
obj* l_Lean_Name_decEq___boxed(obj*, obj*);
obj* l_Lean_Name_quickLt___boxed(obj*, obj*);
obj* l_Lean_mkSimpleName(obj*);
obj* l_Lean_NameMap_find___rarg(obj*, obj*);
obj* l_Lean_mkStrName(obj*, obj*);
obj* l_Lean_Name_DecidableEq;
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Name_append(obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
uint8 l_Lean_Name_quickLtCore(obj*, obj*);
obj* l_Lean_Name_DecidableRel___boxed(obj*, obj*);
obj* l_Lean_Name_append___main___boxed(obj*, obj*);
obj* l_Lean_Name_components_x_27(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_foldl___main___at_String_toName___spec__1(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main___boxed(obj*, obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_Lean_NameMap_find(obj*);
obj* l_Lean_NameMap_Inhabited___boxed(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_NameMap_find___boxed(obj*);
obj* l_Lean_NameSet_contains___boxed(obj*, obj*);
obj* l_Lean_Name_getPrefix(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_mkNameSet;
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_NameMap_insert___rarg(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_mkNameMap(obj*);
obj* l_Lean_Name_getPrefix___boxed(obj*);
obj* l_Lean_NameMap_contains(obj*);
obj* l_Lean_Name_updatePrefix___main(obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_String_trim(obj*);
uint8 l_Lean_Name_quickLtCore___main(obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_NameMap_insert___boxed(obj*);
obj* l_String_split(obj*, obj*);
obj* l_Lean_Name_toStringWithSep(obj*, obj*);
obj* l_Lean_Name_append___boxed(obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_String_toName(obj*);
obj* l_Lean_NameMap_Inhabited(obj*);
obj* l_Lean_NameSet_Inhabited;
obj* l_Lean_Name_getPrefix___main(obj*);
obj* l_Lean_Name_components_x_27___main(obj*);
uint8 l_Lean_Name_DecidableRel(obj*, obj*);
obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Name_replacePrefix(obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix___main___boxed(obj*);
obj* l_Lean_mkNameMap___boxed(obj*);
obj* l_List_foldl___main___at_String_toName___spec__1___boxed(obj*, obj*);
obj* l_Lean_Name_replacePrefix___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Name_HasAppend;
obj* l_Lean_NameSet_insert(obj*, obj*);
obj* l_Lean_NameMap_HasEmptyc___boxed(obj*);
obj* l_Lean_NameMap_contains___rarg___boxed(obj*, obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Name_quickLtCore___main___boxed(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___boxed(obj*, obj*);
obj* l_Lean_mkNumName(obj*, obj*);
obj* l_Lean_Name_toString(obj*);
obj* l_Lean_NameSet_HasEmptyc;
obj* _init_l_Lean_Inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_Lean_mkStrName(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_mkNumName(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_Lean_mkSimpleName(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean_name_mk_string(x_1, x_0);
return x_2;
}
}
obj* _init_l_Lean_stringToName() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkSimpleName), 1, 0);
return x_0;
}
}
obj* l_Lean_Name_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean_name_hash_usize(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_Lean_Name_Hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_hash___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_Name_getPrefix___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
return x_0;
}
default:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
}
}
obj* l_Lean_Name_getPrefix___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Name_getPrefix___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Name_getPrefix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Name_getPrefix___main(x_0);
return x_1;
}
}
obj* l_Lean_Name_getPrefix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Name_getPrefix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Name_updatePrefix___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_1);
return x_0;
}
case 1:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean_name_mk_string(x_1, x_3);
return x_6;
}
default:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean_name_mk_numeral(x_1, x_7);
return x_10;
}
}
}
}
obj* l_Lean_Name_updatePrefix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_updatePrefix___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Name_components_x_27___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean_name_mk_string(x_7, x_4);
x_9 = l_Lean_Name_components_x_27___main(x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
default:
{
obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::box(0);
x_17 = lean_name_mk_numeral(x_16, x_13);
x_18 = l_Lean_Name_components_x_27___main(x_11);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
}
obj* l_Lean_Name_components_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Name_components_x_27___main(x_0);
return x_1;
}
}
obj* l_Lean_Name_components(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Name_components_x_27___main(x_0);
x_2 = l_List_reverse___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Name_decEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_name_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Name_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_decEq___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Name_append___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::inc(x_0);
return x_0;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_Lean_Name_append___main(x_0, x_3);
x_9 = lean_name_mk_string(x_8, x_5);
return x_9;
}
default:
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = l_Lean_Name_append___main(x_0, x_10);
x_16 = lean_name_mk_numeral(x_15, x_12);
return x_16;
}
}
}
}
obj* l_Lean_Name_append___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_append___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Name_append(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_append___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Name_append___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_append(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_Lean_Name_HasAppend() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_append___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_Name_replacePrefix___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_3; 
x_3 = lean_name_dec_eq(x_1, x_0);
if (x_3 == 0)
{
return x_0;
}
else
{
lean::inc(x_2);
return x_2;
}
}
case 1:
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
x_11 = l_Lean_Name_replacePrefix___main(x_5, x_1, x_2);
x_12 = lean_name_mk_string(x_11, x_7);
return x_12;
}
else
{
lean::dec(x_5);
lean::dec(x_7);
lean::inc(x_2);
return x_2;
}
}
default:
{
obj* x_16; obj* x_18; uint8 x_20; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean_name_dec_eq(x_0, x_1);
lean::dec(x_0);
if (x_20 == 0)
{
obj* x_22; obj* x_23; 
x_22 = l_Lean_Name_replacePrefix___main(x_16, x_1, x_2);
x_23 = lean_name_mk_numeral(x_22, x_18);
return x_23;
}
else
{
lean::dec(x_16);
lean::dec(x_18);
lean::inc(x_2);
return x_2;
}
}
}
}
}
obj* l_Lean_Name_replacePrefix___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Name_replacePrefix___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Name_replacePrefix(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Name_replacePrefix___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Name_replacePrefix___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Name_replacePrefix(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Lean_Name_quickLtCore___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
x_2 = lean_name_dec_eq(x_1, x_0);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::string_dec_lt(x_6, x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = lean::string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
return x_9;
}
else
{
x_0 = x_5;
x_1 = x_7;
goto _start;
}
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
default:
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
}
}
default:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
case 1:
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
default:
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_0, 0);
x_17 = lean::cnstr_get(x_0, 1);
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::nat_dec_lt(x_17, x_19);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = lean::nat_dec_eq(x_17, x_19);
if (x_21 == 0)
{
return x_20;
}
else
{
x_0 = x_16;
x_1 = x_18;
goto _start;
}
}
else
{
uint8 x_23; 
x_23 = 1;
return x_23;
}
}
}
}
}
}
}
obj* l_Lean_Name_quickLtCore___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Name_quickLtCore___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Name_quickLtCore(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Name_quickLtCore___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Name_quickLtCore___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Name_quickLtCore(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Name_quickLt(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; 
x_2 = lean_name_hash_usize(x_0);
x_3 = lean_name_hash_usize(x_1);
x_4 = x_2 < x_3;
if (x_4 == 0)
{
uint8 x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_Lean_Name_quickLtCore___main(x_0, x_1);
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
obj* l_Lean_Name_quickLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Name_quickLt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Name_hasLtQuick() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_Lean_Name_DecidableRel(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Name_quickLt(x_0, x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Lean_Name_DecidableRel___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Name_DecidableRel(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Name_toStringWithSep___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[anonymous]");
return x_0;
}
}
obj* l_Lean_Name_toStringWithSep___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Name_toStringWithSep___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; uint8 x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean_name_dec_eq(x_3, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = l_Lean_Name_toStringWithSep___main(x_0, x_3);
x_11 = lean::string_append(x_10, x_0);
x_12 = lean::string_append(x_11, x_5);
lean::dec(x_5);
return x_12;
}
else
{
lean::dec(x_3);
return x_5;
}
}
default:
{
obj* x_15; obj* x_17; obj* x_20; uint8 x_21; 
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::box(0);
x_21 = lean_name_dec_eq(x_15, x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_Lean_Name_toStringWithSep___main(x_0, x_15);
x_23 = lean::string_append(x_22, x_0);
x_24 = l_Nat_repr(x_17);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
return x_25;
}
else
{
obj* x_28; 
lean::dec(x_15);
x_28 = l_Nat_repr(x_17);
return x_28;
}
}
}
}
}
obj* l_Lean_Name_toStringWithSep___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_toStringWithSep___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Name_toStringWithSep(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_toStringWithSep___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Name_toStringWithSep___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_toStringWithSep(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_Lean_Name_toString___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".");
return x_0;
}
}
obj* l_Lean_Name_toString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = l_Lean_Name_toStringWithSep___main(x_1, x_0);
return x_2;
}
}
obj* _init_l_Lean_Name_HasToString() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_toString), 1, 0);
return x_0;
}
}
obj* l_Lean_mkNameMap(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_mkNameMap___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_mkNameMap(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_HasEmptyc(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_NameMap_HasEmptyc___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameMap_HasEmptyc(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_NameMap_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameMap_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
x_4 = l_RBNode_insert___rarg(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_NameMap_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_NameMap_insert___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_NameMap_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameMap_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_NameMap_contains___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
return x_0;
}
}
uint8 l_Lean_NameMap_contains___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_NameMap_contains___rarg___closed__1;
x_3 = l_RBNode_find___main___rarg(x_2, lean::box(0), x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 1;
return x_6;
}
}
}
obj* l_Lean_NameMap_contains(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_NameMap_contains___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_NameMap_contains___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_NameMap_contains___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_NameMap_contains___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameMap_contains(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
x_3 = l_RBNode_find___main___rarg(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l_Lean_NameMap_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_NameMap_find___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_NameMap_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_NameMap_find(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_mkNameSet() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_NameSet_HasEmptyc() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_NameSet_Inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_Lean_NameSet_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
x_3 = lean::box(0);
x_4 = l_RBNode_insert___rarg(x_2, x_0, x_1, x_3);
return x_4;
}
}
uint8 l_Lean_NameSet_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_NameMap_contains___rarg___closed__1;
x_3 = l_RBNode_find___main___rarg(x_2, lean::box(0), x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 1;
return x_6;
}
}
}
obj* l_Lean_NameSet_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_NameSet_contains(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_List_foldl___main___at_String_toName___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_String_trim(x_2);
x_5 = lean_name_mk_string(x_0, x_4);
x_0 = x_5;
x_1 = x_3;
goto _start;
}
}
}
obj* l_String_toName(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = l_String_split(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_String_toName___spec__1(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_foldl___main___at_String_toName___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_String_toName___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_string_basic(obj*);
obj* initialize_init_coe(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_data_hashable(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_data_rbtree_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_name(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashable(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbtree_default(w);
 l_Lean_Inhabited = _init_l_Lean_Inhabited();
lean::mark_persistent(l_Lean_Inhabited);
 l_Lean_stringToName = _init_l_Lean_stringToName();
lean::mark_persistent(l_Lean_stringToName);
 l_Lean_Name_Hashable = _init_l_Lean_Name_Hashable();
lean::mark_persistent(l_Lean_Name_Hashable);
 l_Lean_Name_DecidableEq = _init_l_Lean_Name_DecidableEq();
lean::mark_persistent(l_Lean_Name_DecidableEq);
 l_Lean_Name_HasAppend = _init_l_Lean_Name_HasAppend();
lean::mark_persistent(l_Lean_Name_HasAppend);
 l_Lean_Name_hasLtQuick = _init_l_Lean_Name_hasLtQuick();
lean::mark_persistent(l_Lean_Name_hasLtQuick);
 l_Lean_Name_toStringWithSep___main___closed__1 = _init_l_Lean_Name_toStringWithSep___main___closed__1();
lean::mark_persistent(l_Lean_Name_toStringWithSep___main___closed__1);
 l_Lean_Name_toString___closed__1 = _init_l_Lean_Name_toString___closed__1();
lean::mark_persistent(l_Lean_Name_toString___closed__1);
 l_Lean_Name_HasToString = _init_l_Lean_Name_HasToString();
lean::mark_persistent(l_Lean_Name_HasToString);
 l_Lean_NameMap_contains___rarg___closed__1 = _init_l_Lean_NameMap_contains___rarg___closed__1();
lean::mark_persistent(l_Lean_NameMap_contains___rarg___closed__1);
 l_Lean_mkNameSet = _init_l_Lean_mkNameSet();
lean::mark_persistent(l_Lean_mkNameSet);
 l_Lean_NameSet_HasEmptyc = _init_l_Lean_NameSet_HasEmptyc();
lean::mark_persistent(l_Lean_NameSet_HasEmptyc);
 l_Lean_NameSet_Inhabited = _init_l_Lean_NameSet_Inhabited();
lean::mark_persistent(l_Lean_NameSet_Inhabited);
return w;
}
