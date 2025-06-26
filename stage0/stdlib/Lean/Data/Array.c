// Lean compiler output
// Module: Lean.Data.Array
// Imports: Init.Data.Range
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_11 = lean_box(x_4);
x_12 = lean_array_set(x_8, x_3, x_11);
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_5, lean_box(0), x_14);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_5);
x_17 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_5);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_5, lean_box(0), x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__5___boxed), 9, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
x_14 = lean_unbox(x_10);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_nat_add(x_6, x_1);
lean_dec(x_1);
lean_dec(x_6);
x_16 = lean_box(x_3);
x_17 = lean_array_set(x_7, x_8, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__4), 4, 3);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_4, lean_box(0), x_19);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__6), 4, 3);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_7);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_4, lean_box(0), x_23);
x_25 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_1);
x_25 = lean_box(x_7);
x_26 = lean_array_get(x_25, x_12, x_4);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_box(x_7);
x_29 = lean_array_get(x_28, x_12, x_8);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_14 = x_30;
goto block_24;
}
else
{
x_14 = x_27;
goto block_24;
}
block_24:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_15 = lean_box(1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__7___boxed), 9, 8);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_1);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_11);
lean_closure_set(x_16, 6, x_12);
lean_closure_set(x_16, 7, x_4);
x_17 = lean_array_fget(x_5, x_4);
lean_dec(x_4);
x_18 = lean_array_fget(x_5, x_8);
lean_dec(x_8);
x_19 = lean_apply_2(x_6, x_17, x_18);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_1, lean_box(0), x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_13);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_box(x_6);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__8___boxed), 10, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_10);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_5);
lean_closure_set(x_15, 6, x_14);
x_16 = lean_nat_add(x_10, x_2);
lean_dec(x_10);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 2, x_2);
x_18 = l_Std_Range_forIn_x27_loop___redArg(x_8, x_17, x_15, x_12, x_16);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_box(x_6);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__8___boxed), 10, 7);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_10);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_22);
x_24 = lean_nat_add(x_10, x_2);
lean_dec(x_10);
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Std_Range_forIn_x27_loop___redArg(x_8, x_25, x_23, x_26, x_24);
x_28 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_27, x_9);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_box(x_1);
x_10 = lean_array_get(x_9, x_2, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_fget(x_3, x_6);
x_13 = lean_array_push(x_8, x_12);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__11___boxed), 3, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_4);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_4, lean_box(0), x_15);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__12___boxed), 3, 2);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_4);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_4, lean_box(0), x_19);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_1);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__13___boxed), 8, 5);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
x_14 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_15 = l_Std_Range_forIn_x27_loop___redArg(x_5, x_6, x_13, x_14, x_7);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_array_get_size(x_2);
lean_inc(x_8);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_inc(x_5);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__1), 3, 2);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_5);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__9___boxed), 12, 9);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_7);
lean_closure_set(x_15, 6, x_8);
lean_closure_set(x_15, 7, x_1);
lean_closure_set(x_15, 8, x_14);
lean_inc(x_6);
x_16 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__10), 2, 1);
lean_closure_set(x_16, 0, x_6);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_5);
x_17 = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__14___boxed), 9, 8);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_6);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_1);
lean_closure_set(x_17, 5, x_12);
lean_closure_set(x_17, 6, x_10);
lean_closure_set(x_17, 7, x_16);
x_18 = l_Std_Range_forIn_x27_loop___redArg(x_1, x_12, x_15, x_13, x_10);
x_19 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterPairsM___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterPairsM___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterPairsM___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterPairsM___redArg___lam__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Array_filterPairsM___redArg___lam__5(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Array_filterPairsM___redArg___lam__7(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l_Array_filterPairsM___redArg___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_filterPairsM___redArg___lam__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterPairsM___redArg___lam__11(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterPairsM___redArg___lam__12(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Array_filterPairsM___redArg___lam__13(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Array_filterPairsM___redArg___lam__14(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init_Data_Range(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Array(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
