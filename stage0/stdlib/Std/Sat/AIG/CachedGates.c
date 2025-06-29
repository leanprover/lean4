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
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
return x_21;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkNotCached(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_5; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_66; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_44 = x_4;
} else {
 lean_dec_ref(x_4);
 x_44 = lean_box(0);
}
x_66 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_42);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_box(1);
x_69 = lean_unbox(x_68);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_69);
x_45 = x_42;
goto block_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_42, 0);
lean_inc(x_70);
lean_dec(x_42);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_45 = x_72;
goto block_65;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_box(0);
x_76 = lean_unbox(x_75);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_76);
x_45 = x_42;
goto block_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_unbox(x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_80);
x_45 = x_79;
goto block_65;
}
}
block_41:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_ctor_set(x_6, 1, x_16);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_21 = lean_box(1);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 1, 1);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_29);
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
lean_ctor_set(x_6, 1, x_32);
return x_6;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
block_65:
{
uint8_t x_46; 
x_46 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_box(1);
x_49 = lean_unbox(x_48);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_49);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_43);
x_5 = x_50;
goto block_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_box(1);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_53);
x_5 = x_55;
goto block_41;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_58);
if (lean_is_scalar(x_44)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_44;
}
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_43);
x_5 = x_59;
goto block_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
if (lean_is_scalar(x_44)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_44;
}
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_62);
x_5 = x_64;
goto block_41;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_55 = lean_ctor_get(x_4, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_57 = x_4;
} else {
 lean_dec_ref(x_4);
 x_57 = lean_box(0);
}
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (x_59 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_74);
x_63 = x_55;
goto block_72;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_box(0);
x_76 = lean_unbox(x_75);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_76);
x_63 = x_55;
goto block_72;
}
block_72:
{
if (x_61 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_box(1);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_60);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_65);
x_33 = x_67;
goto block_54;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_68 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 1, 1);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_60);
x_70 = lean_unbox(x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
if (lean_is_scalar(x_57)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_57;
}
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_69);
x_33 = x_71;
goto block_54;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_55, 0);
x_78 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
lean_inc(x_77);
lean_dec(x_55);
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_81 = x_56;
} else {
 lean_dec_ref(x_56);
 x_81 = lean_box(0);
}
if (x_78 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_box(1);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_77);
x_94 = lean_unbox(x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_94);
x_82 = x_93;
goto block_91;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_77);
x_97 = lean_unbox(x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_97);
x_82 = x_96;
goto block_91;
}
block_91:
{
if (x_80 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_83 = lean_box(1);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_79);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
if (lean_is_scalar(x_57)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_57;
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_84);
x_33 = x_86;
goto block_54;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_87 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_79);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_57)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_57;
}
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_88);
x_33 = x_90;
goto block_54;
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
block_29:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_17);
x_5 = x_12;
x_6 = x_13;
x_7 = x_11;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_5 = x_12;
x_6 = x_13;
x_7 = x_20;
goto block_10;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_24);
x_5 = x_12;
x_6 = x_13;
x_7 = x_11;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_5 = x_12;
x_6 = x_13;
x_7 = x_27;
goto block_10;
}
}
}
block_54:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_31, x_33);
x_35 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_40);
x_11 = x_37;
x_12 = x_36;
x_13 = x_32;
goto block_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_11 = x_37;
x_12 = x_36;
x_13 = x_43;
goto block_29;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_49);
x_11 = x_46;
x_12 = x_45;
x_13 = x_32;
goto block_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
lean_dec(x_32);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_11 = x_46;
x_12 = x_45;
x_13 = x_52;
goto block_29;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_58; 
x_58 = !lean_is_exclusive(x_4);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_4, 1);
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
lean_inc(x_62);
if (x_65 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_box(1);
lean_inc(x_64);
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_64);
x_82 = lean_unbox(x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_82);
lean_ctor_set(x_4, 1, x_81);
x_67 = x_4;
goto block_79;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_box(0);
lean_inc(x_64);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_64);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
lean_ctor_set(x_4, 1, x_84);
x_67 = x_4;
goto block_79;
}
block_79:
{
lean_object* x_68; 
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_67);
if (x_63 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(1);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(0, 1, 1);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_62);
x_73 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_30 = x_69;
x_31 = x_65;
x_32 = x_64;
x_33 = x_70;
x_34 = x_72;
goto block_57;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_66;
}
lean_ctor_set(x_77, 0, x_62);
x_78 = lean_unbox(x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_78);
x_30 = x_74;
x_31 = x_65;
x_32 = x_64;
x_33 = x_75;
x_34 = x_77;
goto block_57;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_105; 
x_86 = lean_ctor_get(x_4, 1);
x_87 = lean_ctor_get(x_59, 0);
x_88 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
lean_inc(x_87);
lean_dec(x_59);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
 x_91 = lean_box(0);
}
lean_inc(x_87);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_87);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_88);
if (x_90 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_box(1);
lean_inc(x_89);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_89);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
lean_ctor_set(x_4, 1, x_107);
lean_ctor_set(x_4, 0, x_105);
x_92 = x_4;
goto block_104;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_box(0);
lean_inc(x_89);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_89);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
lean_ctor_set(x_4, 1, x_110);
lean_ctor_set(x_4, 0, x_105);
x_92 = x_4;
goto block_104;
}
block_104:
{
lean_object* x_93; 
lean_inc(x_2);
lean_inc(x_1);
x_93 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_92);
if (x_88 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(1);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(0, 1, 1);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_87);
x_98 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_98);
x_30 = x_94;
x_31 = x_90;
x_32 = x_89;
x_33 = x_95;
x_34 = x_97;
goto block_57;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_102 = lean_alloc_ctor(0, 1, 1);
} else {
 x_102 = x_91;
}
lean_ctor_set(x_102, 0, x_87);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_30 = x_99;
x_31 = x_90;
x_32 = x_89;
x_33 = x_100;
x_34 = x_102;
goto block_57;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_133; 
x_112 = lean_ctor_get(x_4, 0);
x_113 = lean_ctor_get(x_4, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_4);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
lean_inc(x_114);
if (lean_is_scalar(x_116)) {
 x_133 = lean_alloc_ctor(0, 1, 1);
} else {
 x_133 = x_116;
}
lean_ctor_set(x_133, 0, x_114);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_115);
if (x_118 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_134 = lean_box(1);
lean_inc(x_117);
x_135 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_135, 0, x_117);
x_136 = lean_unbox(x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_136);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_135);
x_120 = x_137;
goto block_132;
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; 
x_138 = lean_box(0);
lean_inc(x_117);
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_117);
x_140 = lean_unbox(x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_140);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_133);
lean_ctor_set(x_141, 1, x_139);
x_120 = x_141;
goto block_132;
}
block_132:
{
lean_object* x_121; 
lean_inc(x_2);
lean_inc(x_1);
x_121 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_120);
if (x_115 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(1);
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(0, 1, 1);
} else {
 x_125 = x_119;
}
lean_ctor_set(x_125, 0, x_114);
x_126 = lean_unbox(x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_126);
x_30 = x_122;
x_31 = x_118;
x_32 = x_117;
x_33 = x_123;
x_34 = x_125;
goto block_57;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_dec(x_121);
x_129 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_130 = lean_alloc_ctor(0, 1, 1);
} else {
 x_130 = x_119;
}
lean_ctor_set(x_130, 0, x_114);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_30 = x_127;
x_31 = x_118;
x_32 = x_117;
x_33 = x_128;
x_34 = x_130;
goto block_57;
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
block_29:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_17);
x_5 = x_11;
x_6 = x_13;
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_5 = x_11;
x_6 = x_13;
x_7 = x_20;
goto block_10;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_24);
x_5 = x_11;
x_6 = x_13;
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_5 = x_11;
x_6 = x_13;
x_7 = x_27;
goto block_10;
}
}
}
block_57:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_30, x_36);
x_38 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_43);
x_11 = x_39;
x_12 = x_40;
x_13 = x_33;
goto block_29;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_11 = x_39;
x_12 = x_40;
x_13 = x_46;
goto block_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_52);
x_11 = x_48;
x_12 = x_49;
x_13 = x_33;
goto block_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_33, 0);
lean_inc(x_53);
lean_dec(x_33);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_11 = x_48;
x_12 = x_49;
x_13 = x_55;
goto block_29;
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
lean_object* x_5; uint8_t x_42; 
x_42 = !lean_is_exclusive(x_4);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_4, 1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_48);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(1);
lean_ctor_set(x_43, 0, x_49);
x_52 = lean_unbox(x_51);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_52);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_45);
x_5 = x_4;
goto block_41;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_box(0);
lean_ctor_set(x_43, 0, x_49);
x_54 = lean_unbox(x_53);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_54);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_45);
x_5 = x_4;
goto block_41;
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_56);
if (x_58 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_box(1);
lean_ctor_set(x_43, 0, x_57);
x_61 = lean_unbox(x_60);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_61);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_59);
x_5 = x_4;
goto block_41;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_box(0);
lean_ctor_set(x_43, 0, x_57);
x_63 = lean_unbox(x_62);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_63);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_59);
x_5 = x_4;
goto block_41;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_4, 1);
x_65 = lean_ctor_get(x_43, 0);
x_66 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_inc(x_65);
lean_dec(x_43);
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 1);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_66);
if (x_68 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_67);
x_73 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
lean_ctor_set(x_4, 1, x_72);
lean_ctor_set(x_4, 0, x_70);
x_5 = x_4;
goto block_41;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_67);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
lean_ctor_set(x_4, 1, x_75);
lean_ctor_set(x_4, 0, x_70);
x_5 = x_4;
goto block_41;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get(x_4, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 1, 1);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_80);
if (x_83 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_box(1);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 1, 1);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_82);
x_88 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_88);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_87);
x_5 = x_89;
goto block_41;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_90 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_91 = lean_alloc_ctor(0, 1, 1);
} else {
 x_91 = x_81;
}
lean_ctor_set(x_91, 0, x_82);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_91);
x_5 = x_93;
goto block_41;
}
}
block_41:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_ctor_set(x_6, 1, x_16);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_21 = lean_box(1);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 1, 1);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_29);
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
lean_ctor_set(x_6, 1, x_32);
return x_6;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_38);
return x_40;
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
