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
obj* l_RBNode_setBlack___main___rarg(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Name_HasToString;
obj* l_Lean_Name_toStringWithSep___main___closed__1;
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___boxed(obj*);
obj* l_Lean_NameMap_insert(obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1(obj*);
obj* l_Lean_Name_Hashable;
obj* l_Lean_stringToName;
obj* l_Lean_Name_hasLtQuick;
obj* l_Lean_Name_quickLtCore___boxed(obj*, obj*);
obj* l_Lean_Name_replacePrefix___boxed(obj*, obj*, obj*);
obj* l_Lean_NameMap_contains___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___boxed(obj*);
obj* l_Lean_NameMap_HasEmptyc(obj*);
obj* l_Lean_Name_components(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Name_updatePrefix(obj*, obj*);
obj* l_Lean_Name_hash___boxed(obj*);
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
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
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
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_mkNameSet;
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg(obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_NameMap_insert___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3(obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___boxed(obj*);
obj* l_Lean_mkNameMap(obj*);
obj* l_Lean_Name_getPrefix___boxed(obj*);
obj* l_Lean_NameMap_contains(obj*);
obj* l_Lean_Name_updatePrefix___main(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1(obj*);
obj* l_String_trim(obj*);
uint8 l_Lean_Name_quickLtCore___main(obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_NameMap_insert___boxed(obj*);
obj* l_String_split(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameSet_contains___spec__1___boxed(obj*, obj*);
obj* l_Lean_Name_toStringWithSep(obj*, obj*);
obj* l_Lean_Name_append___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg(obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(obj*, obj*, obj*);
obj* l_String_toName(obj*);
obj* l_Lean_NameMap_Inhabited(obj*);
obj* l_RBNode_find___main___at_Lean_NameSet_contains___spec__1(obj*, obj*);
obj* l_Lean_NameSet_Inhabited;
obj* l_Lean_Name_getPrefix___main(obj*);
obj* l_Lean_Name_components_x_27___main(obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___boxed(obj*);
uint8 l_Lean_Name_DecidableRel(obj*, obj*);
obj* l_Lean_Name_toString___closed__1;
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Name_replacePrefix(obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix___main___boxed(obj*);
obj* l_Lean_mkNameMap___boxed(obj*);
obj* l_List_foldl___main___at_String_toName___spec__1___boxed(obj*, obj*);
obj* l_Lean_Name_replacePrefix___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Name_HasAppend;
obj* l_Lean_NameSet_insert(obj*, obj*);
obj* l_Lean_NameMap_HasEmptyc___boxed(obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_NameMap_contains___rarg___boxed(obj*, obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Name_quickLtCore___main___boxed(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1(obj*);
obj* l_Lean_Name_toStringWithSep___boxed(obj*, obj*);
obj* l_Lean_mkNumName(obj*, obj*);
obj* l_Lean_Name_toString(obj*);
obj* l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_NameSet_HasEmptyc;
obj* l_Lean_NameMap_find___rarg___boxed(obj*, obj*);
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
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___rarg(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_NameMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_0, x_1, x_2);
return x_3;
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
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_NameMap_insert___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1(x_0);
lean::dec(x_0);
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
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
uint8 l_Lean_NameMap_contains___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 1;
return x_5;
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
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_contains___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_NameMap_contains___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
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
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_NameMap_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_NameMap_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_NameMap_find___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameMap_find___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_NameMap_find___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at_Lean_NameMap_find___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_NameMap_find___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_NameMap_find___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
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
obj* l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__2(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_Lean_NameSet_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_NameSet_contains___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
uint8 l_Lean_NameSet_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameSet_contains___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 1;
return x_5;
}
}
}
obj* l_RBNode_find___main___at_Lean_NameSet_contains___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_NameSet_contains___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_NameSet_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_NameSet_contains(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
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
if (io_result_is_error(w)) return w;
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
 l_Lean_mkNameSet = _init_l_Lean_mkNameSet();
lean::mark_persistent(l_Lean_mkNameSet);
 l_Lean_NameSet_HasEmptyc = _init_l_Lean_NameSet_HasEmptyc();
lean::mark_persistent(l_Lean_NameSet_HasEmptyc);
 l_Lean_NameSet_Inhabited = _init_l_Lean_NameSet_Inhabited();
lean::mark_persistent(l_Lean_NameSet_Inhabited);
return w;
}
