// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_Cache_get_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_Sat_AIG_Cache_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Std_Sat_AIG_Cache_get_x3f___rarg(x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_6);
lean_inc(x_8);
x_11 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_8);
x_12 = lean_array_push(x_6, x_8);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
lean_inc(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Std_Sat_AIG_Cache_get_x3f___rarg(x_1, x_2, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_get_size(x_16);
lean_inc(x_18);
x_21 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_16, x_17, x_18);
x_22 = lean_array_push(x_16, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_8, 0, x_4);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Std_Sat_AIG_Cache_get_x3f___rarg(x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_6);
lean_inc(x_8);
x_11 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_8);
x_12 = lean_array_push(x_6, x_8);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_4);
lean_inc(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Std_Sat_AIG_Cache_get_x3f___rarg(x_1, x_2, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_get_size(x_16);
lean_inc(x_18);
x_21 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_16, x_17, x_18);
x_22 = lean_array_push(x_16, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkConstCached___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_8 = x_3;
} else {
 lean_dec_ref(x_3);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_inc(x_12);
lean_inc(x_9);
x_14 = lean_alloc_ctor(2, 2, 2);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 1, x_13);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Std_Sat_AIG_Cache_get_x3f___rarg(x_1, x_2, x_6, x_7, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_get_size(x_6);
x_24 = lean_array_fget(x_6, x_9);
x_25 = lean_array_fget(x_6, x_12);
switch (lean_obj_tag(x_24)) {
case 0:
{
uint8_t x_26; 
lean_dec(x_8);
x_26 = lean_ctor_get_uint8(x_24, 0);
lean_dec(x_24);
if (x_26 == 0)
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_25, 0);
lean_dec(x_25);
if (x_27 == 0)
{
if (x_10 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_7);
x_29 = 0;
x_30 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_28, x_29);
return x_30;
}
else
{
if (x_13 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_7);
x_32 = 0;
x_33 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_31, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_14);
x_34 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_35 = lean_array_push(x_6, x_14);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
return x_37;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_14);
if (x_10 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_7);
x_39 = 0;
x_40 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_38, x_39);
return x_40;
}
else
{
if (x_13 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_7);
lean_inc(x_12);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_7);
x_44 = 0;
x_45 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_43, x_44);
return x_45;
}
}
}
}
else
{
lean_dec(x_25);
if (x_10 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_23);
lean_dec(x_14);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_7);
x_47 = 0;
x_48 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_46, x_47);
return x_48;
}
else
{
if (x_13 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_7);
lean_inc(x_12);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_14);
x_51 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_52 = lean_array_push(x_6, x_14);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_23);
return x_54;
}
}
}
}
else
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_14);
x_55 = lean_ctor_get_uint8(x_25, 0);
lean_dec(x_25);
if (x_55 == 0)
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_7);
x_57 = 0;
x_58 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_56, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_7);
lean_inc(x_9);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_7);
x_62 = 0;
x_63 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_61, x_62);
return x_63;
}
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_7);
lean_inc(x_12);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_7);
x_67 = 0;
x_68 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_66, x_67);
return x_68;
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_7);
x_70 = 0;
x_71 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_69, x_70);
return x_71;
}
}
}
else
{
lean_dec(x_25);
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_6);
lean_ctor_set(x_72, 1, x_7);
lean_inc(x_12);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_eq(x_9, x_12);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_14);
x_75 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_76 = lean_array_push(x_6, x_14);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_23);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
lean_dec(x_23);
lean_dec(x_14);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_7);
x_80 = 0;
x_81 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_79, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
lean_dec(x_23);
lean_dec(x_14);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_6);
lean_ctor_set(x_82, 1, x_7);
x_83 = 0;
x_84 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_82, x_83);
return x_84;
}
}
}
}
case 1:
{
lean_dec(x_24);
switch (lean_obj_tag(x_25)) {
case 0:
{
uint8_t x_85; 
lean_dec(x_8);
x_85 = lean_ctor_get_uint8(x_25, 0);
lean_dec(x_25);
if (x_85 == 0)
{
if (x_10 == 0)
{
lean_dec(x_23);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_6);
lean_ctor_set(x_86, 1, x_7);
x_87 = 0;
x_88 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_86, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_6);
lean_ctor_set(x_89, 1, x_7);
lean_inc(x_9);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
}
else
{
if (x_13 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
lean_dec(x_23);
lean_dec(x_14);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_6);
lean_ctor_set(x_91, 1, x_7);
x_92 = 0;
x_93 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_91, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_inc(x_14);
x_94 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_95 = lean_array_push(x_6, x_14);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_23);
return x_97;
}
}
}
else
{
if (x_10 == 0)
{
lean_dec(x_23);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_6);
lean_ctor_set(x_98, 1, x_7);
lean_inc(x_9);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_9);
return x_99;
}
else
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_6);
lean_ctor_set(x_100, 1, x_7);
x_101 = 0;
x_102 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_100, x_101);
return x_102;
}
}
else
{
if (x_13 == 0)
{
uint8_t x_103; 
x_103 = lean_nat_dec_eq(x_9, x_12);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_inc(x_14);
x_104 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_105 = lean_array_push(x_6, x_14);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_23);
return x_107;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; 
lean_dec(x_23);
lean_dec(x_14);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_7);
x_109 = 0;
x_110 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_108, x_109);
return x_110;
}
}
else
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; 
lean_dec(x_23);
lean_dec(x_14);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_6);
lean_ctor_set(x_111, 1, x_7);
x_112 = 0;
x_113 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_111, x_112);
return x_113;
}
}
}
}
case 1:
{
uint8_t x_114; lean_object* x_115; 
lean_dec(x_25);
lean_dec(x_23);
x_114 = lean_nat_dec_eq(x_9, x_12);
if (x_114 == 0)
{
lean_object* x_126; 
x_126 = lean_box(0);
x_115 = x_126;
goto block_125;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_6);
lean_ctor_set(x_127, 1, x_7);
lean_inc(x_9);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_9);
return x_128;
}
else
{
lean_object* x_129; 
x_129 = lean_box(0);
x_115 = x_129;
goto block_125;
}
}
else
{
lean_object* x_130; 
x_130 = lean_box(0);
x_115 = x_130;
goto block_125;
}
}
block_125:
{
lean_dec(x_115);
if (x_114 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_15 = x_116;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_117; 
x_117 = lean_box(0);
x_15 = x_117;
goto block_21;
}
else
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_14);
lean_dec(x_8);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_6);
lean_ctor_set(x_118, 1, x_7);
x_119 = 0;
x_120 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_118, x_119);
return x_120;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
lean_dec(x_14);
lean_dec(x_8);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_6);
lean_ctor_set(x_121, 1, x_7);
x_122 = 0;
x_123 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_121, x_122);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_box(0);
x_15 = x_124;
goto block_21;
}
}
}
}
}
default: 
{
uint8_t x_131; lean_object* x_132; 
lean_dec(x_25);
lean_dec(x_23);
x_131 = lean_nat_dec_eq(x_9, x_12);
if (x_131 == 0)
{
lean_object* x_143; 
x_143 = lean_box(0);
x_132 = x_143;
goto block_142;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_6);
lean_ctor_set(x_144, 1, x_7);
lean_inc(x_9);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_9);
return x_145;
}
else
{
lean_object* x_146; 
x_146 = lean_box(0);
x_132 = x_146;
goto block_142;
}
}
else
{
lean_object* x_147; 
x_147 = lean_box(0);
x_132 = x_147;
goto block_142;
}
}
block_142:
{
lean_dec(x_132);
if (x_131 == 0)
{
lean_object* x_133; 
x_133 = lean_box(0);
x_15 = x_133;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_15 = x_134;
goto block_21;
}
else
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; 
lean_dec(x_14);
lean_dec(x_8);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_6);
lean_ctor_set(x_135, 1, x_7);
x_136 = 0;
x_137 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_135, x_136);
return x_137;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; 
lean_dec(x_14);
lean_dec(x_8);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_6);
lean_ctor_set(x_138, 1, x_7);
x_139 = 0;
x_140 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_138, x_139);
return x_140;
}
else
{
lean_object* x_141; 
x_141 = lean_box(0);
x_15 = x_141;
goto block_21;
}
}
}
}
}
}
}
default: 
{
lean_dec(x_24);
switch (lean_obj_tag(x_25)) {
case 0:
{
uint8_t x_148; 
lean_dec(x_8);
x_148 = lean_ctor_get_uint8(x_25, 0);
lean_dec(x_25);
if (x_148 == 0)
{
if (x_10 == 0)
{
lean_dec(x_23);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_6);
lean_ctor_set(x_149, 1, x_7);
x_150 = 0;
x_151 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_149, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_6);
lean_ctor_set(x_152, 1, x_7);
lean_inc(x_9);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_9);
return x_153;
}
}
else
{
if (x_13 == 0)
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; 
lean_dec(x_23);
lean_dec(x_14);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_6);
lean_ctor_set(x_154, 1, x_7);
x_155 = 0;
x_156 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_154, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_inc(x_14);
x_157 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_158 = lean_array_push(x_6, x_14);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_23);
return x_160;
}
}
}
else
{
if (x_10 == 0)
{
lean_dec(x_23);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_6);
lean_ctor_set(x_161, 1, x_7);
lean_inc(x_9);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_9);
return x_162;
}
else
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_6);
lean_ctor_set(x_163, 1, x_7);
x_164 = 0;
x_165 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_163, x_164);
return x_165;
}
}
else
{
if (x_13 == 0)
{
uint8_t x_166; 
x_166 = lean_nat_dec_eq(x_9, x_12);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc(x_14);
x_167 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_168 = lean_array_push(x_6, x_14);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_23);
return x_170;
}
else
{
lean_object* x_171; uint8_t x_172; lean_object* x_173; 
lean_dec(x_23);
lean_dec(x_14);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_6);
lean_ctor_set(x_171, 1, x_7);
x_172 = 0;
x_173 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_171, x_172);
return x_173;
}
}
else
{
lean_object* x_174; uint8_t x_175; lean_object* x_176; 
lean_dec(x_23);
lean_dec(x_14);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_6);
lean_ctor_set(x_174, 1, x_7);
x_175 = 0;
x_176 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_174, x_175);
return x_176;
}
}
}
}
case 1:
{
uint8_t x_177; lean_object* x_178; 
lean_dec(x_25);
lean_dec(x_23);
x_177 = lean_nat_dec_eq(x_9, x_12);
if (x_177 == 0)
{
lean_object* x_189; 
x_189 = lean_box(0);
x_178 = x_189;
goto block_188;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_6);
lean_ctor_set(x_190, 1, x_7);
lean_inc(x_9);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_9);
return x_191;
}
else
{
lean_object* x_192; 
x_192 = lean_box(0);
x_178 = x_192;
goto block_188;
}
}
else
{
lean_object* x_193; 
x_193 = lean_box(0);
x_178 = x_193;
goto block_188;
}
}
block_188:
{
lean_dec(x_178);
if (x_177 == 0)
{
lean_object* x_179; 
x_179 = lean_box(0);
x_15 = x_179;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_180; 
x_180 = lean_box(0);
x_15 = x_180;
goto block_21;
}
else
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; 
lean_dec(x_14);
lean_dec(x_8);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_6);
lean_ctor_set(x_181, 1, x_7);
x_182 = 0;
x_183 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_181, x_182);
return x_183;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; 
lean_dec(x_14);
lean_dec(x_8);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_6);
lean_ctor_set(x_184, 1, x_7);
x_185 = 0;
x_186 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_184, x_185);
return x_186;
}
else
{
lean_object* x_187; 
x_187 = lean_box(0);
x_15 = x_187;
goto block_21;
}
}
}
}
}
default: 
{
uint8_t x_194; lean_object* x_195; 
lean_dec(x_25);
lean_dec(x_23);
x_194 = lean_nat_dec_eq(x_9, x_12);
if (x_194 == 0)
{
lean_object* x_206; 
x_206 = lean_box(0);
x_195 = x_206;
goto block_205;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_6);
lean_ctor_set(x_207, 1, x_7);
lean_inc(x_9);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_9);
return x_208;
}
else
{
lean_object* x_209; 
x_209 = lean_box(0);
x_195 = x_209;
goto block_205;
}
}
else
{
lean_object* x_210; 
x_210 = lean_box(0);
x_195 = x_210;
goto block_205;
}
}
block_205:
{
lean_dec(x_195);
if (x_194 == 0)
{
lean_object* x_196; 
x_196 = lean_box(0);
x_15 = x_196;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_197; 
x_197 = lean_box(0);
x_15 = x_197;
goto block_21;
}
else
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; 
lean_dec(x_14);
lean_dec(x_8);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_6);
lean_ctor_set(x_198, 1, x_7);
x_199 = 0;
x_200 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_198, x_199);
return x_200;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_201; uint8_t x_202; lean_object* x_203; 
lean_dec(x_14);
lean_dec(x_8);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_6);
lean_ctor_set(x_201, 1, x_7);
x_202 = 0;
x_203 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_201, x_202);
return x_203;
}
else
{
lean_object* x_204; 
x_204 = lean_box(0);
x_15 = x_204;
goto block_21;
}
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
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_ctor_get(x_22, 0);
lean_inc(x_211);
lean_dec(x_22);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_6);
lean_ctor_set(x_212, 1, x_7);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_16 = lean_array_get_size(x_6);
lean_inc(x_14);
x_17 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_18 = lean_array_push(x_6, x_14);
if (lean_is_scalar(x_8)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_8;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkGateCached_go___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkGateCached_go___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_4, 0, x_7);
x_11 = l_Std_Sat_AIG_mkGateCached_go___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_mkGateCached_go___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_13);
x_19 = l_Std_Sat_AIG_mkGateCached_go___rarg(x_1, x_2, x_3, x_18);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
x_21 = l_Std_Sat_AIG_mkGateCached_go___rarg(x_1, x_2, x_3, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkGateCached___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
