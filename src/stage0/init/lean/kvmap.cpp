// Lean compiler output
// Module: init.lean.kvmap
// Imports: init.lean.name init.data.option.basic init.data.int.default
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
obj* l_Lean_KVMap_subset___main___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_KVMap_getNat(obj*, obj*);
obj* l_Lean_KVMap_getName(obj*, obj*);
obj* l_Lean_KVMap_setBool(obj*, obj*, uint8);
uint8 l_Lean_DataValue_beq(obj*, obj*);
obj* l_Lean_KVMap_subset___boxed(obj*, obj*);
obj* l_Lean_KVMap_getInt(obj*, obj*);
uint8 l_Option_isSome___main___rarg(obj*);
obj* l_Lean_KVMap_getString(obj*, obj*);
obj* l_Lean_DataValue_beq___main___boxed(obj*, obj*);
obj* l_Lean_KVMap_findCore___main(obj*, obj*);
obj* l_Lean_KVMap_findCore(obj*, obj*);
uint8 l_Lean_KVMap_subset___main(obj*, obj*);
obj* l_Lean_KVMap_findCore___boxed(obj*, obj*);
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_Lean_KVMap_find(obj*, obj*);
obj* l_Lean_KVMap_contains___boxed(obj*, obj*);
obj* l_Lean_KVMap_HasBeq;
obj* l_Lean_KVMap_getBool(obj*, obj*);
uint8 l_Lean_KVMap_contains(obj*, obj*);
uint8 l_Lean_KVMap_subset(obj*, obj*);
obj* l_Lean_KVMap_setInt(obj*, obj*, obj*);
obj* l_Lean_KVMap_insert(obj*, obj*, obj*);
obj* l_Lean_DataValue_HasBeq;
obj* l_Lean_KVMap_insert___main(obj*, obj*, obj*);
obj* l_Lean_DataValue_beq___boxed(obj*, obj*);
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
obj* l_Lean_KVMap_setBool___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_KVMap_getInt___boxed(obj*, obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_KVMap_find___boxed(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_KVMap_find___main(obj*, obj*);
obj* l_Lean_KVMap_eqv___boxed(obj*, obj*);
obj* l_Lean_KVMap_find___main___boxed(obj*, obj*);
obj* l_Lean_KVMap_findCore___main___boxed(obj*, obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_KVMap_insertCore___main(obj*, obj*, obj*);
obj* l_Lean_KVMap_getName___boxed(obj*, obj*);
obj* l_Lean_KVMap_getBool___boxed(obj*, obj*);
obj* l_Lean_KVMap_getString___boxed(obj*, obj*);
obj* l_Lean_KVMap_insertCore(obj*, obj*, obj*);
obj* l_Lean_KVMap_getNat___boxed(obj*, obj*);
uint8 l_Lean_DataValue_beq___main(obj*, obj*);
uint8 l_Lean_DataValue_beq___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
default:
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
case 1:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::nat_dec_eq(x_8, x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
default:
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
}
}
case 2:
{
uint8 x_13; 
x_13 = lean::cnstr_get_scalar<uint8>(x_0, 0);
switch (lean::obj_tag(x_1)) {
case 2:
{
uint8 x_14; 
x_14 = lean::cnstr_get_scalar<uint8>(x_1, 0);
if (x_13 == 0)
{
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
}
else
{
if (x_14 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
}
default:
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
}
}
default:
{
uint8 x_20; 
x_20 = 0;
return x_20;
}
}
}
}
obj* l_Lean_DataValue_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_DataValue_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_DataValue_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_DataValue_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_DataValue_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_DataValue_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_DataValue_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DataValue_beq___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_KVMap_findCore___main(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean_name_dec_eq(x_8, x_1);
lean::dec(x_8);
if (x_13 == 0)
{
lean::dec(x_10);
x_0 = x_5;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_5);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_10);
return x_18;
}
}
}
}
obj* l_Lean_KVMap_findCore___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_findCore(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_KVMap_findCore___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_KVMap_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_find___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_KVMap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_find(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_insertCore___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_12; 
x_5 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_9 = x_0;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean_name_dec_eq(x_10, x_1);
if (x_12 == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_10);
x_14 = l_Lean_KVMap_insertCore___main(x_7, x_1, x_2);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_17 = x_5;
} else {
 lean::dec(x_5);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_2);
if (lean::is_scalar(x_9)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_9;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_7);
return x_19;
}
}
}
}
obj* l_Lean_KVMap_insertCore(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_KVMap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_KVMap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_2);
return x_3;
}
}
uint8 l_Lean_KVMap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
x_3 = l_Option_isSome___main___rarg(x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_KVMap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_KVMap_contains(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_KVMap_getString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_KVMap_getString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_getString(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_getNat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 1:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_KVMap_getNat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_getNat(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_getInt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 4:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_KVMap_getInt___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_getInt(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_getBool(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 2:
{
uint8 x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get_scalar<uint8>(x_4, 0);
lean::dec(x_4);
x_9 = lean::box(x_7);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_KVMap_getBool___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_getBool(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_getName(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 3:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_KVMap_getName___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_KVMap_getName(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_KVMap_setString(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_KVMap_setNat(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_KVMap_setInt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_KVMap_setBool(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_cnstr(2, 0, 1);
lean::cnstr_set_scalar(x_3, 0, x_2);
x_4 = x_3;
x_5 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_4);
return x_5;
}
}
obj* l_Lean_KVMap_setBool___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_Lean_KVMap_setBool(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_KVMap_setName(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_Lean_KVMap_insertCore___main(x_0, x_1, x_3);
return x_4;
}
}
uint8 l_Lean_KVMap_subset___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_1);
x_9 = l_Lean_KVMap_findCore___main(x_1, x_6);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_11; 
lean::dec(x_1);
x_11 = 0;
return x_11;
}
else
{
obj* x_12; uint8 x_15; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_Lean_DataValue_beq___main(x_7, x_12);
lean::dec(x_12);
if (x_15 == 0)
{
lean::dec(x_1);
return x_15;
}
else
{
x_0 = x_5;
goto _start;
}
}
}
}
}
obj* l_Lean_KVMap_subset___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_KVMap_subset___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_Lean_KVMap_subset(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_KVMap_subset___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_KVMap_subset___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_KVMap_subset(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_Lean_KVMap_eqv(obj* x_0, obj* x_1) {
_start:
{
uint8 x_3; 
lean::inc(x_1);
x_3 = l_Lean_KVMap_subset___main(x_0, x_1);
if (x_3 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_3;
}
else
{
uint8 x_6; 
x_6 = l_Lean_KVMap_subset___main(x_1, x_0);
lean::dec(x_1);
return x_6;
}
}
}
obj* l_Lean_KVMap_eqv___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_KVMap_eqv(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_KVMap_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_KVMap_eqv___boxed), 2, 0);
return x_0;
}
}
obj* initialize_init_lean_name(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_data_int_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_kvmap(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_int_default(w);
 l_Lean_DataValue_HasBeq = _init_l_Lean_DataValue_HasBeq();
lean::mark_persistent(l_Lean_DataValue_HasBeq);
 l_Lean_KVMap_HasBeq = _init_l_Lean_KVMap_HasBeq();
lean::mark_persistent(l_Lean_KVMap_HasBeq);
return w;
}
