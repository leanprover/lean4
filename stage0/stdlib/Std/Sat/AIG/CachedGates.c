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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkNotCached___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* x_5; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_44 = 1;
lean_ctor_set(x_37, 0, x_41);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_44);
if (x_43 == 0)
{
lean_object* x_45; 
lean_ctor_set(x_36, 0, x_42);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_36);
x_5 = x_45;
goto block_35;
}
else
{
uint8_t x_46; lean_object* x_47; 
x_46 = 0;
lean_ctor_set(x_36, 0, x_42);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_36);
x_5 = x_47;
goto block_35;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_inc(x_49);
lean_dec(x_37);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
if (x_50 == 0)
{
lean_object* x_53; 
lean_ctor_set(x_36, 0, x_49);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_36);
x_5 = x_53;
goto block_35;
}
else
{
uint8_t x_54; lean_object* x_55; 
x_54 = 0;
lean_ctor_set(x_36, 0, x_49);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_36);
x_5 = x_55;
goto block_35;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_36, 0);
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
 x_59 = lean_box(0);
}
x_60 = 1;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
if (x_58 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_5 = x_63;
goto block_35;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_5 = x_66;
goto block_35;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_36, 0);
x_70 = lean_ctor_get(x_37, 0);
x_71 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_72 = 0;
lean_ctor_set(x_37, 0, x_69);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_72);
if (x_71 == 0)
{
uint8_t x_73; lean_object* x_74; 
x_73 = 1;
lean_ctor_set(x_36, 0, x_70);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_37);
lean_ctor_set(x_74, 1, x_36);
x_5 = x_74;
goto block_35;
}
else
{
lean_object* x_75; 
lean_ctor_set(x_36, 0, x_70);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_36);
x_5 = x_75;
goto block_35;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_36, 0);
x_77 = lean_ctor_get(x_37, 0);
x_78 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_inc(x_77);
lean_dec(x_37);
x_79 = 0;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
if (x_78 == 0)
{
uint8_t x_81; lean_object* x_82; 
x_81 = 1;
lean_ctor_set(x_36, 0, x_77);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_81);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_36);
x_5 = x_82;
goto block_35;
}
else
{
lean_object* x_83; 
lean_ctor_set(x_36, 0, x_77);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_36);
x_5 = x_83;
goto block_35;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_36, 0);
lean_inc(x_84);
lean_dec(x_36);
x_85 = lean_ctor_get(x_37, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_87 = x_37;
} else {
 lean_dec_ref(x_37);
 x_87 = lean_box(0);
}
x_88 = 0;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
if (x_86 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_90 = 1;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_5 = x_92;
goto block_35;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_88);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
x_5 = x_94;
goto block_35;
}
}
}
block_35:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_5);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_18 = x_8;
} else {
 lean_dec_ref(x_8);
 x_18 = lean_box(0);
}
if (x_13 == 0)
{
uint8_t x_69; 
x_69 = 1;
lean_ctor_set(x_7, 0, x_12);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_69);
if (x_15 == 0)
{
lean_object* x_70; 
lean_ctor_set(x_6, 0, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_6);
x_19 = x_70;
goto block_68;
}
else
{
uint8_t x_71; lean_object* x_72; 
x_71 = 0;
lean_ctor_set(x_6, 0, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_7);
lean_ctor_set(x_72, 1, x_6);
x_19 = x_72;
goto block_68;
}
}
else
{
uint8_t x_73; 
x_73 = 0;
lean_ctor_set(x_7, 0, x_12);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_73);
if (x_15 == 0)
{
uint8_t x_74; lean_object* x_75; 
x_74 = 1;
lean_ctor_set(x_6, 0, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_7);
lean_ctor_set(x_75, 1, x_6);
x_19 = x_75;
goto block_68;
}
else
{
lean_object* x_76; 
lean_ctor_set(x_6, 0, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_7);
lean_ctor_set(x_76, 1, x_6);
x_19 = x_76;
goto block_68;
}
}
block_68:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_9, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (x_17 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_26 = 1;
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_26);
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_18)) {
 x_27 = lean_alloc_ctor(0, 1, 1);
} else {
 x_27 = x_18;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_22, x_28);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
if (lean_is_scalar(x_18)) {
 x_31 = lean_alloc_ctor(0, 1, 1);
} else {
 x_31 = x_18;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_22, x_32);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_21);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
if (x_35 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
if (lean_is_scalar(x_18)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_18;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_22, x_39);
return x_40;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = 0;
if (lean_is_scalar(x_18)) {
 x_42 = lean_alloc_ctor(0, 1, 1);
} else {
 x_42 = x_18;
}
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_22, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_20, 0);
lean_inc(x_45);
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_49 = 0;
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_49);
if (x_48 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 1;
if (lean_is_scalar(x_18)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_18;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_21);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_45, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_scalar(x_18)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_18;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_21);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_45, x_55);
return x_56;
}
}
else
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_inc(x_57);
lean_dec(x_21);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_16);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
if (x_58 == 0)
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = 1;
if (lean_is_scalar(x_18)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_18;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_45, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
if (lean_is_scalar(x_18)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_18;
}
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_45, x_66);
return x_67;
}
}
}
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_79 = lean_ctor_get(x_7, 0);
x_80 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_79);
lean_dec(x_7);
x_81 = lean_ctor_get(x_8, 0);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_83 = x_8;
} else {
 lean_dec_ref(x_8);
 x_83 = lean_box(0);
}
if (x_78 == 0)
{
uint8_t x_114; lean_object* x_115; 
x_114 = 1;
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_77);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
if (x_80 == 0)
{
lean_object* x_116; 
lean_ctor_set(x_6, 0, x_79);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_6);
x_84 = x_116;
goto block_113;
}
else
{
uint8_t x_117; lean_object* x_118; 
x_117 = 0;
lean_ctor_set(x_6, 0, x_79);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_117);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_6);
x_84 = x_118;
goto block_113;
}
}
else
{
uint8_t x_119; lean_object* x_120; 
x_119 = 0;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_77);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
if (x_80 == 0)
{
uint8_t x_121; lean_object* x_122; 
x_121 = 1;
lean_ctor_set(x_6, 0, x_79);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_121);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_6);
x_84 = x_122;
goto block_113;
}
else
{
lean_object* x_123; 
lean_ctor_set(x_6, 0, x_79);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_6);
x_84 = x_123;
goto block_113;
}
}
block_113:
{
lean_object* x_85; lean_object* x_86; 
lean_inc(x_2);
lean_inc(x_1);
x_85 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_9, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (x_82 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_90 = x_86;
} else {
 lean_dec_ref(x_86);
 x_90 = lean_box(0);
}
x_91 = 1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
if (x_89 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_scalar(x_83)) {
 x_93 = lean_alloc_ctor(0, 1, 1);
} else {
 x_93 = x_83;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_87, x_94);
return x_95;
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = 0;
if (lean_is_scalar(x_83)) {
 x_97 = lean_alloc_ctor(0, 1, 1);
} else {
 x_97 = x_83;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_87, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
lean_dec(x_85);
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_103 = x_86;
} else {
 lean_dec_ref(x_86);
 x_103 = lean_box(0);
}
x_104 = 0;
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 1, 1);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_81);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
if (x_102 == 0)
{
uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = 1;
if (lean_is_scalar(x_83)) {
 x_107 = lean_alloc_ctor(0, 1, 1);
} else {
 x_107 = x_83;
}
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_100, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_scalar(x_83)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_83;
}
lean_ctor_set(x_110, 0, x_101);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_104);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_100, x_111);
return x_112;
}
}
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_6, 0);
x_125 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_124);
lean_dec(x_6);
x_126 = lean_ctor_get(x_7, 0);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_128 = x_7;
} else {
 lean_dec_ref(x_7);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_8, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_131 = x_8;
} else {
 lean_dec_ref(x_8);
 x_131 = lean_box(0);
}
if (x_125 == 0)
{
uint8_t x_162; lean_object* x_163; 
x_162 = 1;
if (lean_is_scalar(x_128)) {
 x_163 = lean_alloc_ctor(0, 1, 1);
} else {
 x_163 = x_128;
}
lean_ctor_set(x_163, 0, x_124);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
if (x_127 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_126);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_132 = x_165;
goto block_161;
}
else
{
uint8_t x_166; lean_object* x_167; lean_object* x_168; 
x_166 = 0;
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_126);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_167);
x_132 = x_168;
goto block_161;
}
}
else
{
uint8_t x_169; lean_object* x_170; 
x_169 = 0;
if (lean_is_scalar(x_128)) {
 x_170 = lean_alloc_ctor(0, 1, 1);
} else {
 x_170 = x_128;
}
lean_ctor_set(x_170, 0, x_124);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_169);
if (x_127 == 0)
{
uint8_t x_171; lean_object* x_172; lean_object* x_173; 
x_171 = 1;
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_126);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_132 = x_173;
goto block_161;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_126);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_169);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_174);
x_132 = x_175;
goto block_161;
}
}
block_161:
{
lean_object* x_133; lean_object* x_134; 
lean_inc(x_2);
lean_inc(x_1);
x_133 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_9, x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (x_130 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_134, sizeof(void*)*1);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_139 = 1;
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 1, 1);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
if (x_137 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
if (lean_is_scalar(x_131)) {
 x_141 = lean_alloc_ctor(0, 1, 1);
} else {
 x_141 = x_131;
}
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_135, x_142);
return x_143;
}
else
{
uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = 0;
if (lean_is_scalar(x_131)) {
 x_145 = lean_alloc_ctor(0, 1, 1);
} else {
 x_145 = x_131;
}
lean_ctor_set(x_145, 0, x_136);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_135, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_133, 0);
lean_inc(x_148);
lean_dec(x_133);
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_134, sizeof(void*)*1);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
x_152 = 0;
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 1, 1);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_129);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
if (x_150 == 0)
{
uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = 1;
if (lean_is_scalar(x_131)) {
 x_155 = lean_alloc_ctor(0, 1, 1);
} else {
 x_155 = x_131;
}
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_148, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_scalar(x_131)) {
 x_158 = lean_alloc_ctor(0, 1, 1);
} else {
 x_158 = x_131;
}
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_152);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_153);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_148, x_159);
return x_160;
}
}
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_12 = x_6;
} else {
 lean_dec_ref(x_6);
 x_12 = lean_box(0);
}
if (x_8 == 0)
{
uint8_t x_85; lean_object* x_86; 
x_85 = 0;
lean_inc(x_7);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_7);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
if (x_11 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_87 = 1;
lean_inc(x_10);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_10);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_13 = x_89;
goto block_84;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_inc(x_10);
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_85);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_90);
x_13 = x_91;
goto block_84;
}
}
else
{
uint8_t x_92; lean_object* x_93; 
x_92 = 1;
lean_inc(x_7);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_7);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
if (x_11 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_inc(x_10);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_13 = x_95;
goto block_84;
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_96 = 0;
lean_inc(x_10);
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
x_13 = x_98;
goto block_84;
}
}
block_84:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
if (x_8 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = 1;
if (lean_is_scalar(x_12)) {
 x_71 = lean_alloc_ctor(0, 1, 1);
} else {
 x_71 = x_12;
}
lean_ctor_set(x_71, 0, x_7);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
if (x_11 == 0)
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_72 = 0;
if (lean_is_scalar(x_9)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_9;
}
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_20 = x_74;
goto block_69;
}
else
{
lean_object* x_75; lean_object* x_76; 
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_10);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_20 = x_76;
goto block_69;
}
}
else
{
uint8_t x_77; lean_object* x_78; 
x_77 = 0;
if (lean_is_scalar(x_12)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_12;
}
lean_ctor_set(x_78, 0, x_7);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
if (x_11 == 0)
{
lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_9)) {
 x_79 = lean_alloc_ctor(0, 1, 1);
} else {
 x_79 = x_9;
}
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_20 = x_80;
goto block_69;
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_81 = 1;
if (lean_is_scalar(x_9)) {
 x_82 = lean_alloc_ctor(0, 1, 1);
} else {
 x_82 = x_9;
}
lean_ctor_set(x_82, 0, x_10);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_20 = x_83;
goto block_69;
}
}
block_69:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_16, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (x_18 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_27 = 1;
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_27);
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
if (lean_is_scalar(x_19)) {
 x_28 = lean_alloc_ctor(0, 1, 1);
} else {
 x_28 = x_19;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_23, x_29);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
if (lean_is_scalar(x_19)) {
 x_32 = lean_alloc_ctor(0, 1, 1);
} else {
 x_32 = x_19;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_23, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_22);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
if (x_36 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_19)) {
 x_39 = lean_alloc_ctor(0, 1, 1);
} else {
 x_39 = x_19;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_23, x_40);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = 0;
if (lean_is_scalar(x_19)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_19;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_23, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec(x_21);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_50 = 0;
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_50);
if (x_49 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = 1;
if (lean_is_scalar(x_19)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_19;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_46, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
if (lean_is_scalar(x_19)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_19;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_22);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_46, x_56);
return x_57;
}
}
else
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_22, 0);
x_59 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_inc(x_58);
lean_dec(x_22);
x_60 = 0;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
if (x_59 == 0)
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = 1;
if (lean_is_scalar(x_19)) {
 x_63 = lean_alloc_ctor(0, 1, 1);
} else {
 x_63 = x_19;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_46, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
if (lean_is_scalar(x_19)) {
 x_66 = lean_alloc_ctor(0, 1, 1);
} else {
 x_66 = x_19;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_60);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_46, x_67);
return x_68;
}
}
}
}
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
lean_object* x_5; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_44 = 0;
lean_ctor_set(x_37, 0, x_41);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_44);
if (x_43 == 0)
{
uint8_t x_45; lean_object* x_46; 
x_45 = 1;
lean_ctor_set(x_36, 0, x_42);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_36);
x_5 = x_46;
goto block_35;
}
else
{
lean_object* x_47; 
lean_ctor_set(x_36, 0, x_42);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_36);
x_5 = x_47;
goto block_35;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_inc(x_49);
lean_dec(x_37);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
if (x_50 == 0)
{
uint8_t x_53; lean_object* x_54; 
x_53 = 1;
lean_ctor_set(x_36, 0, x_49);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_36);
x_5 = x_54;
goto block_35;
}
else
{
lean_object* x_55; 
lean_ctor_set(x_36, 0, x_49);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_36);
x_5 = x_55;
goto block_35;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_36, 0);
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
 x_59 = lean_box(0);
}
x_60 = 0;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
if (x_58 == 0)
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_62 = 1;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_5 = x_64;
goto block_35;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_60);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_5 = x_66;
goto block_35;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_36, 0);
x_70 = lean_ctor_get(x_37, 0);
x_71 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_72 = 1;
lean_ctor_set(x_37, 0, x_69);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_72);
if (x_71 == 0)
{
lean_object* x_73; 
lean_ctor_set(x_36, 0, x_70);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_36);
x_5 = x_73;
goto block_35;
}
else
{
uint8_t x_74; lean_object* x_75; 
x_74 = 0;
lean_ctor_set(x_36, 0, x_70);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_36);
x_5 = x_75;
goto block_35;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_36, 0);
x_77 = lean_ctor_get(x_37, 0);
x_78 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_inc(x_77);
lean_dec(x_37);
x_79 = 1;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
if (x_78 == 0)
{
lean_object* x_81; 
lean_ctor_set(x_36, 0, x_77);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_36);
x_5 = x_81;
goto block_35;
}
else
{
uint8_t x_82; lean_object* x_83; 
x_82 = 0;
lean_ctor_set(x_36, 0, x_77);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_36);
x_5 = x_83;
goto block_35;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_36, 0);
lean_inc(x_84);
lean_dec(x_36);
x_85 = lean_ctor_get(x_37, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_87 = x_37;
} else {
 lean_dec_ref(x_37);
 x_87 = lean_box(0);
}
x_88 = 1;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
if (x_86 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_5 = x_91;
goto block_35;
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_92 = 0;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
x_5 = x_94;
goto block_35;
}
}
}
block_35:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_5);
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
