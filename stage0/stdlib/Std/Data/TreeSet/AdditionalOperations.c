// Lean compiler output
// Module: Std.Data.TreeSet.AdditionalOperations
// Imports: Std.Data.TreeSet.Basic Std.Data.TreeSet.Raw.Basic Std.Data.TreeMap.AdditionalOperations
#include <lean/lean.h>
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getGE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getLE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getLT(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getGT(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getLE(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getGE(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getGT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_getLT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_3 = x_10;
x_4 = x_6;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___at_Std_TreeMap_getGE___spec__2___rarg(x_1, x_3, x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_7;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getGE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGE___at_Std_TreeMap_getGE___spec__1___rarg(x_1, lean_box(0), x_4, x_3, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getGE(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_TreeMap_getGE___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_3 = x_11;
x_4 = x_6;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_instDecidableEqOrdering(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___at_Std_TreeMap_getGT___spec__2___rarg(x_1, x_3, x_15, x_8);
if (lean_obj_tag(x_16) == 0)
{
return x_7;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getGT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGT___at_Std_TreeMap_getGT___spec__1___rarg(x_1, lean_box(0), x_4, x_3, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getGT(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_TreeMap_getGT___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_8;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___at_Std_TreeMap_getLE___spec__2___rarg(x_1, x_3, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_7;
}
else
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getLE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLE___at_Std_TreeMap_getLE___spec__1___rarg(x_1, lean_box(0), x_4, x_3, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getLE(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_TreeMap_getLE___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_3 = x_11;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = 2;
x_13 = l_instDecidableEqOrdering(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_8;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___at_Std_TreeMap_getLT___spec__2___rarg(x_1, x_3, x_15, x_9);
if (lean_obj_tag(x_16) == 0)
{
return x_7;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getLT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLT___at_Std_TreeMap_getLT___spec__1___rarg(x_1, lean_box(0), x_4, x_3, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_getLT(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_TreeMap_getLT___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_TreeMap_AdditionalOperations(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_AdditionalOperations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
