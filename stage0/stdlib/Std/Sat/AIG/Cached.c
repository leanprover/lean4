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
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget(x_6, x_9);
x_24 = lean_array_fget(x_6, x_12);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_25; 
lean_dec(x_8);
x_25 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_25 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_24, 0);
lean_dec(x_24);
if (x_26 == 0)
{
if (x_10 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
x_28 = 0;
x_29 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_27, x_28);
return x_29;
}
else
{
if (x_13 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
x_31 = 0;
x_32 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_30, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_get_size(x_6);
lean_inc(x_14);
x_34 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_35 = lean_array_push(x_6, x_14);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
else
{
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
lean_dec(x_24);
if (x_10 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_array_get_size(x_6);
lean_inc(x_14);
x_52 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_53 = lean_array_push(x_6, x_14);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_56; 
lean_dec(x_14);
x_56 = lean_ctor_get_uint8(x_24, 0);
lean_dec(x_24);
if (x_56 == 0)
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_6);
lean_ctor_set(x_57, 1, x_7);
x_58 = 0;
x_59 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_57, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_7);
lean_inc(x_9);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_9);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_7);
x_63 = 0;
x_64 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_62, x_63);
return x_64;
}
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
lean_inc(x_12);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_12);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_7);
x_68 = 0;
x_69 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_67, x_68);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_7);
x_71 = 0;
x_72 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_70, x_71);
return x_72;
}
}
}
else
{
lean_dec(x_24);
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_7);
lean_inc(x_12);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_12);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_eq(x_9, x_12);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_array_get_size(x_6);
lean_inc(x_14);
x_77 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_78 = lean_array_push(x_6, x_14);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
lean_dec(x_14);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_6);
lean_ctor_set(x_81, 1, x_7);
x_82 = 0;
x_83 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_81, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
lean_dec(x_14);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_7);
x_85 = 0;
x_86 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_84, x_85);
return x_86;
}
}
}
}
case 1:
{
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 0:
{
uint8_t x_87; 
lean_dec(x_8);
x_87 = lean_ctor_get_uint8(x_24, 0);
lean_dec(x_24);
if (x_87 == 0)
{
if (x_10 == 0)
{
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_6);
lean_ctor_set(x_88, 1, x_7);
x_89 = 0;
x_90 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_88, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_6);
lean_ctor_set(x_91, 1, x_7);
lean_inc(x_9);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_9);
return x_92;
}
}
else
{
if (x_13 == 0)
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_14);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_7);
x_94 = 0;
x_95 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_93, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_array_get_size(x_6);
lean_inc(x_14);
x_97 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_98 = lean_array_push(x_6, x_14);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
else
{
if (x_10 == 0)
{
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_6);
lean_ctor_set(x_101, 1, x_7);
lean_inc(x_9);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_9);
return x_102;
}
else
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_6);
lean_ctor_set(x_103, 1, x_7);
x_104 = 0;
x_105 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_103, x_104);
return x_105;
}
}
else
{
if (x_13 == 0)
{
uint8_t x_106; 
x_106 = lean_nat_dec_eq(x_9, x_12);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_array_get_size(x_6);
lean_inc(x_14);
x_108 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_109 = lean_array_push(x_6, x_14);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; 
lean_dec(x_14);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_6);
lean_ctor_set(x_112, 1, x_7);
x_113 = 0;
x_114 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_112, x_113);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; 
lean_dec(x_14);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_6);
lean_ctor_set(x_115, 1, x_7);
x_116 = 0;
x_117 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_115, x_116);
return x_117;
}
}
}
}
case 1:
{
uint8_t x_118; lean_object* x_119; 
lean_dec(x_24);
x_118 = lean_nat_dec_eq(x_9, x_12);
if (x_118 == 0)
{
lean_object* x_130; 
x_130 = lean_box(0);
x_119 = x_130;
goto block_129;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_6);
lean_ctor_set(x_131, 1, x_7);
lean_inc(x_9);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_9);
return x_132;
}
else
{
lean_object* x_133; 
x_133 = lean_box(0);
x_119 = x_133;
goto block_129;
}
}
else
{
lean_object* x_134; 
x_134 = lean_box(0);
x_119 = x_134;
goto block_129;
}
}
block_129:
{
lean_dec(x_119);
if (x_118 == 0)
{
lean_object* x_120; 
x_120 = lean_box(0);
x_15 = x_120;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_121; 
x_121 = lean_box(0);
x_15 = x_121;
goto block_21;
}
else
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
lean_dec(x_14);
lean_dec(x_8);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_6);
lean_ctor_set(x_122, 1, x_7);
x_123 = 0;
x_124 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_122, x_123);
return x_124;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; 
lean_dec(x_14);
lean_dec(x_8);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_6);
lean_ctor_set(x_125, 1, x_7);
x_126 = 0;
x_127 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_125, x_126);
return x_127;
}
else
{
lean_object* x_128; 
x_128 = lean_box(0);
x_15 = x_128;
goto block_21;
}
}
}
}
}
default: 
{
uint8_t x_135; lean_object* x_136; 
lean_dec(x_24);
x_135 = lean_nat_dec_eq(x_9, x_12);
if (x_135 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_136 = x_147;
goto block_146;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_6);
lean_ctor_set(x_148, 1, x_7);
lean_inc(x_9);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_9);
return x_149;
}
else
{
lean_object* x_150; 
x_150 = lean_box(0);
x_136 = x_150;
goto block_146;
}
}
else
{
lean_object* x_151; 
x_151 = lean_box(0);
x_136 = x_151;
goto block_146;
}
}
block_146:
{
lean_dec(x_136);
if (x_135 == 0)
{
lean_object* x_137; 
x_137 = lean_box(0);
x_15 = x_137;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_15 = x_138;
goto block_21;
}
else
{
lean_object* x_139; uint8_t x_140; lean_object* x_141; 
lean_dec(x_14);
lean_dec(x_8);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_6);
lean_ctor_set(x_139, 1, x_7);
x_140 = 0;
x_141 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_139, x_140);
return x_141;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; 
lean_dec(x_14);
lean_dec(x_8);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_6);
lean_ctor_set(x_142, 1, x_7);
x_143 = 0;
x_144 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_142, x_143);
return x_144;
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_15 = x_145;
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
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 0:
{
uint8_t x_152; 
lean_dec(x_8);
x_152 = lean_ctor_get_uint8(x_24, 0);
lean_dec(x_24);
if (x_152 == 0)
{
if (x_10 == 0)
{
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_6);
lean_ctor_set(x_153, 1, x_7);
x_154 = 0;
x_155 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_153, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_6);
lean_ctor_set(x_156, 1, x_7);
lean_inc(x_9);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_9);
return x_157;
}
}
else
{
if (x_13 == 0)
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; 
lean_dec(x_14);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_6);
lean_ctor_set(x_158, 1, x_7);
x_159 = 0;
x_160 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_158, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_array_get_size(x_6);
lean_inc(x_14);
x_162 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_163 = lean_array_push(x_6, x_14);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
return x_165;
}
}
}
else
{
if (x_10 == 0)
{
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_6);
lean_ctor_set(x_166, 1, x_7);
lean_inc(x_9);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_9);
return x_167;
}
else
{
lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_6);
lean_ctor_set(x_168, 1, x_7);
x_169 = 0;
x_170 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_168, x_169);
return x_170;
}
}
else
{
if (x_13 == 0)
{
uint8_t x_171; 
x_171 = lean_nat_dec_eq(x_9, x_12);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_array_get_size(x_6);
lean_inc(x_14);
x_173 = l_Std_Sat_AIG_Cache_insert___rarg(x_1, x_2, x_6, x_7, x_14);
x_174 = lean_array_push(x_6, x_14);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
else
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; 
lean_dec(x_14);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_6);
lean_ctor_set(x_177, 1, x_7);
x_178 = 0;
x_179 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_177, x_178);
return x_179;
}
}
else
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; 
lean_dec(x_14);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_6);
lean_ctor_set(x_180, 1, x_7);
x_181 = 0;
x_182 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_180, x_181);
return x_182;
}
}
}
}
case 1:
{
uint8_t x_183; lean_object* x_184; 
lean_dec(x_24);
x_183 = lean_nat_dec_eq(x_9, x_12);
if (x_183 == 0)
{
lean_object* x_195; 
x_195 = lean_box(0);
x_184 = x_195;
goto block_194;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_6);
lean_ctor_set(x_196, 1, x_7);
lean_inc(x_9);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_9);
return x_197;
}
else
{
lean_object* x_198; 
x_198 = lean_box(0);
x_184 = x_198;
goto block_194;
}
}
else
{
lean_object* x_199; 
x_199 = lean_box(0);
x_184 = x_199;
goto block_194;
}
}
block_194:
{
lean_dec(x_184);
if (x_183 == 0)
{
lean_object* x_185; 
x_185 = lean_box(0);
x_15 = x_185;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_15 = x_186;
goto block_21;
}
else
{
lean_object* x_187; uint8_t x_188; lean_object* x_189; 
lean_dec(x_14);
lean_dec(x_8);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_6);
lean_ctor_set(x_187, 1, x_7);
x_188 = 0;
x_189 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_187, x_188);
return x_189;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_190; uint8_t x_191; lean_object* x_192; 
lean_dec(x_14);
lean_dec(x_8);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_6);
lean_ctor_set(x_190, 1, x_7);
x_191 = 0;
x_192 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_190, x_191);
return x_192;
}
else
{
lean_object* x_193; 
x_193 = lean_box(0);
x_15 = x_193;
goto block_21;
}
}
}
}
}
default: 
{
uint8_t x_200; lean_object* x_201; 
lean_dec(x_24);
x_200 = lean_nat_dec_eq(x_9, x_12);
if (x_200 == 0)
{
lean_object* x_212; 
x_212 = lean_box(0);
x_201 = x_212;
goto block_211;
}
else
{
if (x_10 == 0)
{
if (x_13 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_6);
lean_ctor_set(x_213, 1, x_7);
lean_inc(x_9);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_9);
return x_214;
}
else
{
lean_object* x_215; 
x_215 = lean_box(0);
x_201 = x_215;
goto block_211;
}
}
else
{
lean_object* x_216; 
x_216 = lean_box(0);
x_201 = x_216;
goto block_211;
}
}
block_211:
{
lean_dec(x_201);
if (x_200 == 0)
{
lean_object* x_202; 
x_202 = lean_box(0);
x_15 = x_202;
goto block_21;
}
else
{
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_15 = x_203;
goto block_21;
}
else
{
lean_object* x_204; uint8_t x_205; lean_object* x_206; 
lean_dec(x_14);
lean_dec(x_8);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_6);
lean_ctor_set(x_204, 1, x_7);
x_205 = 0;
x_206 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_204, x_205);
return x_206;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
lean_dec(x_14);
lean_dec(x_8);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_6);
lean_ctor_set(x_207, 1, x_7);
x_208 = 0;
x_209 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_207, x_208);
return x_209;
}
else
{
lean_object* x_210; 
x_210 = lean_box(0);
x_15 = x_210;
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
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_22, 0);
lean_inc(x_217);
lean_dec(x_22);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_6);
lean_ctor_set(x_218, 1, x_7);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
return x_219;
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
