// Lean compiler output
// Module: Std.Sat.AIG.CachedGates
// Imports: Std.Sat.AIG.Cached Std.Sat.AIG.CachedLemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 0;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_5);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_6);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_5);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_BinaryInput_asGateInput___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryInput_asGateInput___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Std_Sat_AIG_BinaryInput_asGateInput___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_8);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_9);
x_11 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_8);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_12, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_15, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_29, x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_24);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_32, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkOrCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = 0;
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_8);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_12, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_14);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_19, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = 0;
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_32, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_34);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_39, x_43);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkXorCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = 0;
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = 1;
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_10);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_13, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_10);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_19, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = 0;
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = 1;
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_29);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_33, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_29);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_39, x_43);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkBEqCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_13, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_8);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_16, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_30, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_24);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_33, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkImpCached___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Cached(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
