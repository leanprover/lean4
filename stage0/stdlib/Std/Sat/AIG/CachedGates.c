// Lean compiler output
// Module: Std.Sat.AIG.CachedGates
// Imports: public import Std.Sat.AIG.CachedLemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkNotCached(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_56; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_37);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_38 = x_4;
} else {
 lean_dec_ref(x_4);
 x_38 = lean_box(0);
}
x_56 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_36);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = 1;
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_58);
x_39 = x_36;
goto block_55;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = 1;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_39 = x_61;
goto block_55;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_36);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_63);
x_39 = x_36;
goto block_55;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_36, 0);
lean_inc(x_64);
lean_dec(x_36);
x_65 = 0;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_39 = x_66;
goto block_55;
}
}
block_35:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 1, x_15);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_18 = x_7;
} else {
 lean_dec_ref(x_7);
 x_18 = lean_box(0);
}
x_19 = 1;
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 1, 1);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_6, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_25);
return x_6;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
lean_ctor_set(x_6, 1, x_28);
return x_6;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_31 = x_7;
} else {
 lean_dec_ref(x_7);
 x_31 = lean_box(0);
}
x_32 = 0;
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
block_55:
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
x_42 = 1;
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_42);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_37);
x_5 = x_43;
goto block_35;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_38)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_38;
}
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
x_5 = x_47;
goto block_35;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_49);
if (lean_is_scalar(x_38)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_38;
}
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_37);
x_5 = x_50;
goto block_35;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_37, 0);
lean_inc(x_51);
lean_dec(x_37);
x_52 = 0;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
if (lean_is_scalar(x_38)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_38;
}
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_53);
x_5 = x_54;
goto block_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkOrCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_26 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
x_47 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_49 = x_4;
} else {
 lean_dec_ref(x_4);
 x_49 = lean_box(0);
}
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
 x_54 = lean_box(0);
}
if (x_51 == 0)
{
uint8_t x_63; 
x_63 = 1;
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_63);
x_55 = x_47;
goto block_62;
}
else
{
uint8_t x_64; 
x_64 = 0;
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_64);
x_55 = x_47;
goto block_62;
}
block_62:
{
if (x_53 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = 1;
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
if (lean_is_scalar(x_49)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_49;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_29 = x_58;
goto block_46;
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_59 = 0;
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 1, 1);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
if (lean_is_scalar(x_49)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_49;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_29 = x_61;
goto block_46;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_inc(x_65);
lean_dec(x_47);
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
 x_69 = lean_box(0);
}
if (x_66 == 0)
{
uint8_t x_78; lean_object* x_79; 
x_78 = 1;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_70 = x_79;
goto block_77;
}
else
{
uint8_t x_80; lean_object* x_81; 
x_80 = 0;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_65);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_70 = x_81;
goto block_77;
}
block_77:
{
if (x_68 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 1;
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 1);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
if (lean_is_scalar(x_49)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_49;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_29 = x_73;
goto block_46;
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_74 = 0;
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
if (lean_is_scalar(x_49)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_49;
}
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
x_29 = x_76;
goto block_46;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_6, x_8);
return x_9;
}
block_25:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_16);
x_5 = x_13;
x_6 = x_12;
x_7 = x_11;
goto block_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_5 = x_13;
x_6 = x_12;
x_7 = x_19;
goto block_10;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_21);
x_5 = x_13;
x_6 = x_12;
x_7 = x_11;
goto block_10;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_5 = x_13;
x_6 = x_12;
x_7 = x_24;
goto block_10;
}
}
}
block_46:
{
lean_object* x_30; uint8_t x_31; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_30 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_27, x_29);
x_31 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_30);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 1;
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_35);
x_11 = x_33;
x_12 = x_32;
x_13 = x_28;
goto block_25;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_11 = x_33;
x_12 = x_32;
x_13 = x_38;
goto block_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_40);
lean_dec_ref(x_30);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_42);
x_11 = x_40;
x_12 = x_39;
x_13 = x_28;
goto block_25;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec(x_28);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_11 = x_40;
x_12 = x_39;
x_13 = x_45;
goto block_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkXorCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_50; 
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_4, 0);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_4, 1);
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
lean_inc(x_54);
if (x_57 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = 1;
lean_inc(x_56);
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
lean_ctor_set(x_4, 1, x_71);
x_59 = x_4;
goto block_69;
}
else
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
lean_inc(x_56);
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
lean_ctor_set(x_4, 1, x_73);
x_59 = x_4;
goto block_69;
}
block_69:
{
lean_object* x_60; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_60 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_59);
if (x_55 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
lean_dec_ref(x_60);
x_63 = 1;
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_26 = x_61;
x_27 = x_56;
x_28 = x_57;
x_29 = x_62;
x_30 = x_64;
goto block_49;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_66);
lean_dec_ref(x_60);
x_67 = 0;
if (lean_is_scalar(x_58)) {
 x_68 = lean_alloc_ctor(0, 1, 1);
} else {
 x_68 = x_58;
}
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_26 = x_65;
x_27 = x_56;
x_28 = x_57;
x_29 = x_66;
x_30 = x_68;
goto block_49;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_91; 
x_74 = lean_ctor_get(x_4, 1);
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_74, sizeof(void*)*1);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
lean_inc(x_75);
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_76);
if (x_78 == 0)
{
uint8_t x_92; lean_object* x_93; 
x_92 = 1;
lean_inc(x_77);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
lean_ctor_set(x_4, 1, x_93);
lean_ctor_set(x_4, 0, x_91);
x_80 = x_4;
goto block_90;
}
else
{
uint8_t x_94; lean_object* x_95; 
x_94 = 0;
lean_inc(x_77);
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_77);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
lean_ctor_set(x_4, 1, x_95);
lean_ctor_set(x_4, 0, x_91);
x_80 = x_4;
goto block_90;
}
block_90:
{
lean_object* x_81; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_81 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_80);
if (x_76 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_81);
x_84 = 1;
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 1, 1);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_26 = x_82;
x_27 = x_77;
x_28 = x_78;
x_29 = x_83;
x_30 = x_85;
goto block_49;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_87);
lean_dec_ref(x_81);
x_88 = 0;
if (lean_is_scalar(x_79)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_79;
}
lean_ctor_set(x_89, 0, x_75);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_26 = x_86;
x_27 = x_77;
x_28 = x_78;
x_29 = x_87;
x_30 = x_89;
goto block_49;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_115; 
x_96 = lean_ctor_get(x_4, 0);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_4);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_97, sizeof(void*)*1);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_103 = x_97;
} else {
 lean_dec_ref(x_97);
 x_103 = lean_box(0);
}
lean_inc(x_98);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 1, 1);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_99);
if (x_102 == 0)
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_116 = 1;
lean_inc(x_101);
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_101);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_104 = x_118;
goto block_114;
}
else
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_119 = 0;
lean_inc(x_101);
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
x_104 = x_121;
goto block_114;
}
block_114:
{
lean_object* x_105; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_105 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_104);
if (x_99 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc_ref(x_107);
lean_dec_ref(x_105);
x_108 = 1;
if (lean_is_scalar(x_103)) {
 x_109 = lean_alloc_ctor(0, 1, 1);
} else {
 x_109 = x_103;
}
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_26 = x_106;
x_27 = x_101;
x_28 = x_102;
x_29 = x_107;
x_30 = x_109;
goto block_49;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc_ref(x_111);
lean_dec_ref(x_105);
x_112 = 0;
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 1, 1);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_26 = x_110;
x_27 = x_101;
x_28 = x_102;
x_29 = x_111;
x_30 = x_113;
goto block_49;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_5, x_8);
return x_9;
}
block_25:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_16);
x_5 = x_11;
x_6 = x_13;
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_5 = x_11;
x_6 = x_13;
x_7 = x_19;
goto block_10;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_21);
x_5 = x_11;
x_6 = x_13;
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_5 = x_11;
x_6 = x_13;
x_7 = x_24;
goto block_10;
}
}
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_33 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_26, x_32);
x_34 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_33);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 1;
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_38);
x_11 = x_35;
x_12 = x_36;
x_13 = x_29;
goto block_25;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = 1;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_11 = x_35;
x_12 = x_36;
x_13 = x_41;
goto block_25;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_33);
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 0;
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_45);
x_11 = x_42;
x_12 = x_43;
x_13 = x_29;
goto block_25;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
lean_dec(x_29);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_11 = x_42;
x_12 = x_43;
x_13 = x_48;
goto block_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkBEqCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_ctor_set(x_39, 0, x_41);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 1;
lean_ctor_set(x_37, 0, x_43);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_45);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_39);
x_5 = x_4;
goto block_35;
}
else
{
uint8_t x_46; 
x_46 = 0;
lean_ctor_set(x_37, 0, x_43);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_46);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_39);
x_5 = x_4;
goto block_35;
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_48);
if (x_50 == 0)
{
uint8_t x_52; 
x_52 = 1;
lean_ctor_set(x_37, 0, x_49);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_52);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_51);
x_5 = x_4;
goto block_35;
}
else
{
uint8_t x_53; 
x_53 = 0;
lean_ctor_set(x_37, 0, x_49);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_53);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_51);
x_5 = x_4;
goto block_35;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_4, 1);
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 1);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_56);
if (x_58 == 0)
{
uint8_t x_61; lean_object* x_62; 
x_61 = 1;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
lean_ctor_set(x_4, 1, x_62);
lean_ctor_set(x_4, 0, x_60);
x_5 = x_4;
goto block_35;
}
else
{
uint8_t x_63; lean_object* x_64; 
x_63 = 0;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
lean_ctor_set(x_4, 1, x_64);
lean_ctor_set(x_4, 0, x_60);
x_5 = x_4;
goto block_35;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_4);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_72 = x_66;
} else {
 lean_dec_ref(x_66);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_68);
if (x_71 == 0)
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_74 = 1;
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_5 = x_76;
goto block_35;
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_77 = 0;
if (lean_is_scalar(x_69)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_69;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_5 = x_79;
goto block_35;
}
}
block_35:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 1, x_15);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_18 = x_7;
} else {
 lean_dec_ref(x_7);
 x_18 = lean_box(0);
}
x_19 = 1;
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 1, 1);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_6, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_25);
return x_6;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
lean_ctor_set(x_6, 1, x_28);
return x_6;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_31 = x_7;
} else {
 lean_dec_ref(x_7);
 x_31 = lean_box(0);
}
x_32 = 0;
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 1);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkImpCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
