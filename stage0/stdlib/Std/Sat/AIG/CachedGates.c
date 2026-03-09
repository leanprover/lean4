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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
if (x_6 == 0)
{
x_8 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_4);
x_8 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_9; 
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
x_15 = x_2;
x_16 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
if (x_16 == 0)
{
x_18 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_14);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_8 = x_5;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
if (x_9 == 0)
{
x_11 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_7);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 0);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
x_18 = x_5;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
if (x_19 == 0)
{
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
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
lean_object* x_5; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_97; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
x_97 = !lean_is_exclusive(x_4);
if (x_97 == 0)
{
x_48 = x_4;
x_49 = x_97;
goto block_96;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_box(0);
x_49 = x_97;
goto block_96;
}
block_45:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_25; 
x_9 = lean_ctor_get(x_6, 0);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_10 = x_6;
x_11 = x_25;
goto block_24;
}
else
{
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_13 = x_7;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
if (x_14 == 0)
{
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_12);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_16);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_43; 
x_27 = lean_ctor_get(x_6, 0);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_6, 1);
lean_dec(x_44);
x_28 = x_6;
x_29 = x_43;
goto block_42;
}
else
{
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_41; 
x_30 = lean_ctor_get(x_7, 0);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_31 = x_7;
x_32 = x_41;
goto block_40;
}
else
{
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_33; lean_object* x_34; 
x_33 = 0;
if (x_32 == 0)
{
x_34 = x_31;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_30);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_34);
x_35 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
block_96:
{
lean_object* x_50; uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_86; 
x_78 = lean_ctor_get(x_46, 0);
x_86 = !lean_is_exclusive(x_46);
if (x_86 == 0)
{
x_79 = x_46;
x_80 = x_86;
goto block_85;
}
else
{
lean_inc(x_78);
lean_dec(x_46);
x_79 = lean_box(0);
x_80 = x_86;
goto block_85;
}
block_85:
{
uint8_t x_81; lean_object* x_82; 
x_81 = 1;
if (x_80 == 0)
{
x_82 = x_79;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_78);
x_82 = x_84;
goto block_83;
}
block_83:
{
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_50 = x_82;
goto block_76;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_95; 
x_87 = lean_ctor_get(x_46, 0);
x_95 = !lean_is_exclusive(x_46);
if (x_95 == 0)
{
x_88 = x_46;
x_89 = x_95;
goto block_94;
}
else
{
lean_inc(x_87);
lean_dec(x_46);
x_88 = lean_box(0);
x_89 = x_95;
goto block_94;
}
block_94:
{
uint8_t x_90; lean_object* x_91; 
x_90 = 0;
if (x_89 == 0)
{
x_91 = x_88;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_87);
x_91 = x_93;
goto block_92;
}
block_92:
{
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_50 = x_91;
goto block_76;
}
}
}
block_76:
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_63; 
x_52 = lean_ctor_get(x_47, 0);
x_63 = !lean_is_exclusive(x_47);
if (x_63 == 0)
{
x_53 = x_47;
x_54 = x_63;
goto block_62;
}
else
{
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_box(0);
x_54 = x_63;
goto block_62;
}
block_62:
{
uint8_t x_55; lean_object* x_56; 
x_55 = 1;
if (x_54 == 0)
{
x_56 = x_53;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_52);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_56);
lean_ctor_set(x_48, 0, x_50);
x_57 = x_48;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
x_5 = x_57;
goto block_45;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_75; 
x_64 = lean_ctor_get(x_47, 0);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
x_65 = x_47;
x_66 = x_75;
goto block_74;
}
else
{
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_box(0);
x_66 = x_75;
goto block_74;
}
block_74:
{
uint8_t x_67; lean_object* x_68; 
x_67 = 0;
if (x_66 == 0)
{
x_68 = x_65;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_64);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_68);
lean_ctor_set(x_48, 0, x_50);
x_69 = x_48;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
x_5 = x_69;
goto block_45;
}
}
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_104; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_34 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_34);
x_63 = lean_ctor_get(x_4, 0);
x_64 = lean_ctor_get(x_4, 1);
x_104 = !lean_is_exclusive(x_4);
if (x_104 == 0)
{
x_65 = x_4;
x_66 = x_104;
goto block_103;
}
else
{
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_4);
x_65 = lean_box(0);
x_66 = x_104;
goto block_103;
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
block_33:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_11, 0);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
x_16 = x_11;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
if (x_17 == 0)
{
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_15);
x_19 = x_21;
goto block_20;
}
block_20:
{
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_5 = x_12;
x_6 = x_13;
x_7 = x_19;
goto block_10;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_32; 
x_24 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_25 = x_11;
x_26 = x_32;
goto block_31;
}
else
{
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = x_32;
goto block_31;
}
block_31:
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
if (x_26 == 0)
{
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_24);
x_28 = x_30;
goto block_29;
}
block_29:
{
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_5 = x_12;
x_6 = x_13;
x_7 = x_28;
goto block_10;
}
}
}
}
block_62:
{
lean_object* x_38; uint8_t x_39; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_38 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_35, x_37);
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_50; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_38);
x_42 = lean_ctor_get(x_36, 0);
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
x_43 = x_36;
x_44 = x_50;
goto block_49;
}
else
{
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = x_50;
goto block_49;
}
block_49:
{
uint8_t x_45; lean_object* x_46; 
x_45 = 1;
if (x_44 == 0)
{
x_46 = x_43;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_42);
x_46 = x_48;
goto block_47;
}
block_47:
{
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_11 = x_41;
x_12 = x_40;
x_13 = x_46;
goto block_33;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_61; 
x_51 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_52);
lean_dec_ref(x_38);
x_53 = lean_ctor_get(x_36, 0);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
x_54 = x_36;
x_55 = x_61;
goto block_60;
}
else
{
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_61;
goto block_60;
}
block_60:
{
uint8_t x_56; lean_object* x_57; 
x_56 = 0;
if (x_55 == 0)
{
x_57 = x_54;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_53);
x_57 = x_59;
goto block_58;
}
block_58:
{
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_11 = x_52;
x_12 = x_51;
x_13 = x_57;
goto block_33;
}
}
}
}
block_103:
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; uint8_t x_102; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
x_102 = !lean_is_exclusive(x_63);
if (x_102 == 0)
{
x_69 = x_63;
x_70 = x_102;
goto block_101;
}
else
{
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_box(0);
x_70 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_100; 
x_71 = lean_ctor_get(x_64, 0);
x_72 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
x_100 = !lean_is_exclusive(x_64);
if (x_100 == 0)
{
x_73 = x_64;
x_74 = x_100;
goto block_99;
}
else
{
lean_inc(x_71);
lean_dec(x_64);
x_73 = lean_box(0);
x_74 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_75; 
if (x_68 == 0)
{
uint8_t x_91; lean_object* x_92; 
x_91 = 1;
if (x_70 == 0)
{
x_92 = x_69;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_67);
x_92 = x_94;
goto block_93;
}
block_93:
{
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_75 = x_92;
goto block_90;
}
}
else
{
uint8_t x_95; lean_object* x_96; 
x_95 = 0;
if (x_70 == 0)
{
x_96 = x_69;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_67);
x_96 = x_98;
goto block_97;
}
block_97:
{
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_75 = x_96;
goto block_90;
}
}
block_90:
{
if (x_72 == 0)
{
uint8_t x_76; lean_object* x_77; 
x_76 = 1;
if (x_74 == 0)
{
x_77 = x_73;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_71);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
if (x_66 == 0)
{
lean_ctor_set(x_65, 1, x_77);
lean_ctor_set(x_65, 0, x_75);
x_78 = x_65;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
x_37 = x_78;
goto block_62;
}
}
}
else
{
uint8_t x_83; lean_object* x_84; 
x_83 = 0;
if (x_74 == 0)
{
x_84 = x_73;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_71);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
if (x_66 == 0)
{
lean_ctor_set(x_65, 1, x_84);
lean_ctor_set(x_65, 0, x_75);
x_85 = x_65;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
x_37 = x_85;
goto block_62;
}
}
}
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_111; 
x_66 = lean_ctor_get(x_4, 0);
x_67 = lean_ctor_get(x_4, 1);
x_111 = !lean_is_exclusive(x_4);
if (x_111 == 0)
{
x_68 = x_4;
x_69 = x_111;
goto block_110;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_111;
goto block_110;
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
block_33:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_11, 0);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
x_16 = x_11;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
if (x_17 == 0)
{
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_15);
x_19 = x_21;
goto block_20;
}
block_20:
{
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_5 = x_12;
x_6 = x_13;
x_7 = x_19;
goto block_10;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_32; 
x_24 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_25 = x_11;
x_26 = x_32;
goto block_31;
}
else
{
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = x_32;
goto block_31;
}
block_31:
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
if (x_26 == 0)
{
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_24);
x_28 = x_30;
goto block_29;
}
block_29:
{
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_5 = x_12;
x_6 = x_13;
x_7 = x_28;
goto block_10;
}
}
}
}
block_65:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_41 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_35, x_40);
x_42 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_53; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_41);
x_45 = lean_ctor_get(x_36, 0);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
x_46 = x_36;
x_47 = x_53;
goto block_52;
}
else
{
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_box(0);
x_47 = x_53;
goto block_52;
}
block_52:
{
uint8_t x_48; lean_object* x_49; 
x_48 = 1;
if (x_47 == 0)
{
x_49 = x_46;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_45);
x_49 = x_51;
goto block_50;
}
block_50:
{
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_11 = x_44;
x_12 = x_43;
x_13 = x_49;
goto block_33;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_64; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_55);
lean_dec_ref(x_41);
x_56 = lean_ctor_get(x_36, 0);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
x_57 = x_36;
x_58 = x_64;
goto block_63;
}
else
{
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_box(0);
x_58 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_59; lean_object* x_60; 
x_59 = 0;
if (x_58 == 0)
{
x_60 = x_57;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_56);
x_60 = x_62;
goto block_61;
}
block_61:
{
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_11 = x_55;
x_12 = x_54;
x_13 = x_60;
goto block_33;
}
}
}
}
block_110:
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_109; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
x_109 = !lean_is_exclusive(x_66);
if (x_109 == 0)
{
x_72 = x_66;
x_73 = x_109;
goto block_108;
}
else
{
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_box(0);
x_73 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; uint8_t x_107; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
x_107 = !lean_is_exclusive(x_67);
if (x_107 == 0)
{
x_76 = x_67;
x_77 = x_107;
goto block_106;
}
else
{
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_box(0);
x_77 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_78; lean_object* x_93; 
lean_inc(x_70);
if (x_73 == 0)
{
x_93 = x_72;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_70);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_71);
x_93 = x_105;
goto block_104;
}
block_92:
{
lean_object* x_79; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_79 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_78);
if (x_71 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_81);
lean_dec_ref(x_79);
x_82 = 1;
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_70);
x_83 = x_76;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_70);
x_83 = x_85;
goto block_84;
}
block_84:
{
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_34 = x_74;
x_35 = x_80;
x_36 = x_81;
x_37 = x_75;
x_38 = x_83;
goto block_65;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_87);
lean_dec_ref(x_79);
x_88 = 0;
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_70);
x_89 = x_76;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_70);
x_89 = x_91;
goto block_90;
}
block_90:
{
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_34 = x_74;
x_35 = x_86;
x_36 = x_87;
x_37 = x_75;
x_38 = x_89;
goto block_65;
}
}
}
block_104:
{
if (x_75 == 0)
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_94 = 1;
lean_inc(x_74);
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_74);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
if (x_69 == 0)
{
lean_ctor_set(x_68, 1, x_95);
lean_ctor_set(x_68, 0, x_93);
x_96 = x_68;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
x_78 = x_96;
goto block_92;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_99 = 0;
lean_inc(x_74);
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_74);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
if (x_69 == 0)
{
lean_ctor_set(x_68, 1, x_100);
lean_ctor_set(x_68, 0, x_93);
x_101 = x_68;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_100);
x_101 = x_103;
goto block_102;
}
block_102:
{
x_78 = x_101;
goto block_92;
}
}
}
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
lean_object* x_5; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_80; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
x_80 = !lean_is_exclusive(x_4);
if (x_80 == 0)
{
x_48 = x_4;
x_49 = x_80;
goto block_79;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_box(0);
x_49 = x_80;
goto block_79;
}
block_45:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_25; 
x_9 = lean_ctor_get(x_6, 0);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_10 = x_6;
x_11 = x_25;
goto block_24;
}
else
{
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_13 = x_7;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
if (x_14 == 0)
{
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_12);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_16);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_43; 
x_27 = lean_ctor_get(x_6, 0);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_6, 1);
lean_dec(x_44);
x_28 = x_6;
x_29 = x_43;
goto block_42;
}
else
{
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_41; 
x_30 = lean_ctor_get(x_7, 0);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_31 = x_7;
x_32 = x_41;
goto block_40;
}
else
{
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_33; lean_object* x_34; 
x_33 = 0;
if (x_32 == 0)
{
x_34 = x_31;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_30);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_34);
x_35 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
block_79:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; uint8_t x_78; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
x_52 = x_46;
x_53 = x_78;
goto block_77;
}
else
{
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_box(0);
x_53 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_76; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_76 = !lean_is_exclusive(x_47);
if (x_76 == 0)
{
x_56 = x_47;
x_57 = x_76;
goto block_75;
}
else
{
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_box(0);
x_57 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_58; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 0, x_50);
x_58 = x_56;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_50);
x_58 = x_74;
goto block_73;
}
block_73:
{
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_51);
if (x_55 == 0)
{
uint8_t x_59; lean_object* x_60; 
x_59 = 1;
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_54);
x_60 = x_52;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_54);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_60);
lean_ctor_set(x_48, 0, x_58);
x_61 = x_48;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
x_5 = x_61;
goto block_45;
}
}
}
else
{
uint8_t x_66; lean_object* x_67; 
x_66 = 0;
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_54);
x_67 = x_52;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_54);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_67);
lean_ctor_set(x_48, 0, x_58);
x_68 = x_48;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
x_5 = x_68;
goto block_45;
}
}
}
}
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
lean_object* runtime_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_CachedGates(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_CachedGates(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_CachedGates(builtin);
}
#ifdef __cplusplus
}
#endif
