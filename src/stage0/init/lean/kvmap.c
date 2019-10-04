// Lean compiler output
// Module: Init.Lean.KVMap
// Imports: Init.Lean.Name Init.Data.Option.Basic Init.Data.Int.Default
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_KVMap_HasBeq___closed__1;
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KVMap_intVal___closed__1;
uint8_t l_Lean_DataValue_beq(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_subset___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getInt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_stringVal___closed__2;
lean_object* l_Lean_KVMap_getString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore___main(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_nameVal___closed__1;
lean_object* l_Lean_KVMap_findD(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_boolVal;
lean_object* l_Lean_KVMap_findCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_intVal___closed__3;
lean_object* l_Lean_KVMap_subsetAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_natVal___closed__1;
uint8_t l_Lean_KVMap_subsetAux___main(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_contains___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_HasBeq;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_DataValue_HasBeq___closed__1;
uint8_t l_Lean_KVMap_subset(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_boolVal___closed__1;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DataValue_HasBeq;
lean_object* l_Lean_DataValue_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_stringVal;
lean_object* l_Lean_KVMap_natVal___closed__3;
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_nameVal___closed__2;
lean_object* l_Lean_name2DataValue(lean_object*);
lean_object* l_Lean_bool2DataValue(uint8_t);
lean_object* l_Lean_KVMap_stringVal___closed__1;
lean_object* l_Lean_KVMap_stringVal___closed__3;
lean_object* l_Lean_KVMap_setBool___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_string2DataValue(lean_object*);
lean_object* l_Lean_KVMap_getInt___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findD___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_int2DataValue(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_get___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_bool2DataValue___boxed(lean_object*);
uint8_t l_Lean_KVMap_subsetAux(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_nameVal;
lean_object* l_Lean_KVMap_nameVal___closed__3;
lean_object* l_Lean_KVMap_findCore___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Int_zero;
lean_object* l_Lean_KVMap_boolVal___closed__3;
lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_get(lean_object*);
lean_object* l_Lean_KVMap_insertCore___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_natVal___closed__2;
lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getBool___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_boolVal___closed__2;
lean_object* l_Lean_KVMap_getString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_intVal;
lean_object* l_Lean_KVMap_intVal___closed__2;
lean_object* l_Lean_KVMap_getNat___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nat2DataValue(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_KVMap_natVal;
uint8_t l_Lean_DataValue_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, 0);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, 0);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, 0);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_nat_dec_eq(x_15, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
default: 
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
}
lean_object* l_Lean_DataValue_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_DataValue_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_DataValue_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_DataValue_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_DataValue_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_DataValue_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_string2DataValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_bool2DataValue(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_bool2DataValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_bool2DataValue(x_2);
return x_3;
}
}
lean_object* l_Lean_name2DataValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_nat2DataValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_int2DataValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_KVMap_findCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_dec_eq(x_6, x_2);
if (x_8 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
lean_object* l_Lean_KVMap_findCore___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_KVMap_findCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_KVMap_findCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_KVMap_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_KVMap_find___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_find(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_KVMap_findD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
lean_object* l_Lean_KVMap_findD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findD(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_KVMap_insertCore___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_name_dec_eq(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l_Lean_KVMap_insertCore___main(x_8, x_2, x_3);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_ctor_set(x_7, 1, x_3);
return x_1;
}
else
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_name_dec_eq(x_18, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_20 = l_Lean_KVMap_insertCore___main(x_17, x_2, x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
}
}
lean_object* l_Lean_KVMap_insertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_KVMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_3);
return x_4;
}
}
uint8_t l_Lean_KVMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_KVMap_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_KVMap_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_KVMap_getString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Lean_KVMap_getString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_getString(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_KVMap_getNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Lean_KVMap_getNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_KVMap_getInt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Lean_KVMap_getInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_getInt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
uint8_t l_Lean_KVMap_getBool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
lean_object* l_Lean_KVMap_getBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_KVMap_getBool(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_KVMap_getName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_findCore___main(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Lean_KVMap_getName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_KVMap_getName(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_KVMap_setString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_KVMap_setNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_KVMap_setInt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_KVMap_setBool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_4, 0, x_3);
x_5 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_KVMap_setBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_KVMap_setBool(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_KVMap_setName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_KVMap_insertCore___main(x_1, x_2, x_4);
return x_5;
}
}
uint8_t l_Lean_KVMap_subsetAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_KVMap_findCore___main(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_DataValue_beq(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
x_1 = x_5;
goto _start;
}
}
}
}
}
lean_object* l_Lean_KVMap_subsetAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_KVMap_subsetAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_KVMap_subsetAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_KVMap_subsetAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_KVMap_subsetAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_KVMap_subset(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_KVMap_subsetAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_KVMap_subset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_KVMap_subset(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_KVMap_eqv(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_KVMap_subsetAux___main(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_KVMap_subsetAux___main(x_2, x_1);
return x_5;
}
}
}
lean_object* l_Lean_KVMap_eqv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_KVMap_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_KVMap_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_eqv___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_KVMap_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_KVMap_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_KVMap_get___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_KVMap_boolVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_setBool___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_boolVal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_getBool___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_boolVal___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_KVMap_boolVal___closed__1;
x_3 = l_Lean_KVMap_boolVal___closed__2;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_KVMap_boolVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_boolVal___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_natVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_setNat), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_natVal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_getNat___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_natVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_KVMap_natVal___closed__1;
x_3 = l_Lean_KVMap_natVal___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_KVMap_natVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_natVal___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_intVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_setInt), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_intVal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_getInt___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_intVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Int_zero;
x_2 = l_Lean_KVMap_intVal___closed__1;
x_3 = l_Lean_KVMap_intVal___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_KVMap_intVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_intVal___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_nameVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_setName), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_nameVal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_getName___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_nameVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_KVMap_nameVal___closed__1;
x_3 = l_Lean_KVMap_nameVal___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_KVMap_nameVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_nameVal___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_stringVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_setString), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_stringVal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_getString___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_KVMap_stringVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_Lean_KVMap_stringVal___closed__1;
x_3 = l_Lean_KVMap_stringVal___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_KVMap_stringVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_stringVal___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Lean_Name(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Data_Int_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_KVMap(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Name(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Int_Default(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_DataValue_HasBeq___closed__1 = _init_l_Lean_DataValue_HasBeq___closed__1();
lean_mark_persistent(l_Lean_DataValue_HasBeq___closed__1);
l_Lean_DataValue_HasBeq = _init_l_Lean_DataValue_HasBeq();
lean_mark_persistent(l_Lean_DataValue_HasBeq);
l_Lean_KVMap_HasBeq___closed__1 = _init_l_Lean_KVMap_HasBeq___closed__1();
lean_mark_persistent(l_Lean_KVMap_HasBeq___closed__1);
l_Lean_KVMap_HasBeq = _init_l_Lean_KVMap_HasBeq();
lean_mark_persistent(l_Lean_KVMap_HasBeq);
l_Lean_KVMap_boolVal___closed__1 = _init_l_Lean_KVMap_boolVal___closed__1();
lean_mark_persistent(l_Lean_KVMap_boolVal___closed__1);
l_Lean_KVMap_boolVal___closed__2 = _init_l_Lean_KVMap_boolVal___closed__2();
lean_mark_persistent(l_Lean_KVMap_boolVal___closed__2);
l_Lean_KVMap_boolVal___closed__3 = _init_l_Lean_KVMap_boolVal___closed__3();
lean_mark_persistent(l_Lean_KVMap_boolVal___closed__3);
l_Lean_KVMap_boolVal = _init_l_Lean_KVMap_boolVal();
lean_mark_persistent(l_Lean_KVMap_boolVal);
l_Lean_KVMap_natVal___closed__1 = _init_l_Lean_KVMap_natVal___closed__1();
lean_mark_persistent(l_Lean_KVMap_natVal___closed__1);
l_Lean_KVMap_natVal___closed__2 = _init_l_Lean_KVMap_natVal___closed__2();
lean_mark_persistent(l_Lean_KVMap_natVal___closed__2);
l_Lean_KVMap_natVal___closed__3 = _init_l_Lean_KVMap_natVal___closed__3();
lean_mark_persistent(l_Lean_KVMap_natVal___closed__3);
l_Lean_KVMap_natVal = _init_l_Lean_KVMap_natVal();
lean_mark_persistent(l_Lean_KVMap_natVal);
l_Lean_KVMap_intVal___closed__1 = _init_l_Lean_KVMap_intVal___closed__1();
lean_mark_persistent(l_Lean_KVMap_intVal___closed__1);
l_Lean_KVMap_intVal___closed__2 = _init_l_Lean_KVMap_intVal___closed__2();
lean_mark_persistent(l_Lean_KVMap_intVal___closed__2);
l_Lean_KVMap_intVal___closed__3 = _init_l_Lean_KVMap_intVal___closed__3();
lean_mark_persistent(l_Lean_KVMap_intVal___closed__3);
l_Lean_KVMap_intVal = _init_l_Lean_KVMap_intVal();
lean_mark_persistent(l_Lean_KVMap_intVal);
l_Lean_KVMap_nameVal___closed__1 = _init_l_Lean_KVMap_nameVal___closed__1();
lean_mark_persistent(l_Lean_KVMap_nameVal___closed__1);
l_Lean_KVMap_nameVal___closed__2 = _init_l_Lean_KVMap_nameVal___closed__2();
lean_mark_persistent(l_Lean_KVMap_nameVal___closed__2);
l_Lean_KVMap_nameVal___closed__3 = _init_l_Lean_KVMap_nameVal___closed__3();
lean_mark_persistent(l_Lean_KVMap_nameVal___closed__3);
l_Lean_KVMap_nameVal = _init_l_Lean_KVMap_nameVal();
lean_mark_persistent(l_Lean_KVMap_nameVal);
l_Lean_KVMap_stringVal___closed__1 = _init_l_Lean_KVMap_stringVal___closed__1();
lean_mark_persistent(l_Lean_KVMap_stringVal___closed__1);
l_Lean_KVMap_stringVal___closed__2 = _init_l_Lean_KVMap_stringVal___closed__2();
lean_mark_persistent(l_Lean_KVMap_stringVal___closed__2);
l_Lean_KVMap_stringVal___closed__3 = _init_l_Lean_KVMap_stringVal___closed__3();
lean_mark_persistent(l_Lean_KVMap_stringVal___closed__3);
l_Lean_KVMap_stringVal = _init_l_Lean_KVMap_stringVal();
lean_mark_persistent(l_Lean_KVMap_stringVal);
return w;
}
#ifdef __cplusplus
}
#endif
