// Lean compiler output
// Module: Std.Sat.AIG.CachedLemmas
// Imports: Std.Sat.AIG.Cached
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
lean_dec(x_1);
x_14 = lean_box(x_12);
x_15 = lean_box(x_13);
x_16 = lean_apply_5(x_4, x_10, x_11, x_14, x_15, lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__2_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = lean_ctor_get_uint8(x_1, 0);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, 0);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
if (x_3 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
if (x_4 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_17 = lean_box(x_4);
x_18 = lean_apply_2(x_6, x_2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_ctor_set_uint8(x_2, 0, x_3);
x_19 = lean_box(x_4);
x_20 = lean_apply_2(x_6, x_2, x_19);
return x_20;
}
}
else
{
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_21, 0, x_4);
x_22 = lean_box(x_4);
x_23 = lean_apply_2(x_6, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_24, 0, x_3);
x_25 = lean_box(x_4);
x_26 = lean_apply_2(x_6, x_24, x_25);
return x_26;
}
}
}
else
{
lean_dec(x_6);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_13);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_28 = lean_box(x_3);
x_29 = lean_apply_4(x_8, x_2, x_28, lean_box(0), lean_box(0));
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_30, 0, x_4);
x_31 = lean_box(x_3);
x_32 = lean_apply_4(x_8, x_30, x_31, lean_box(0), lean_box(0));
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_33 = lean_box(x_4);
x_34 = lean_box(x_4);
lean_inc(x_2);
x_35 = lean_apply_12(x_13, x_2, x_2, x_33, x_34, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_35;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_8);
if (x_3 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(x_4);
x_37 = lean_apply_2(x_6, x_2, x_36);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_39 = lean_box(x_4);
x_40 = lean_apply_2(x_6, x_2, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_41, 0, x_4);
x_42 = lean_box(x_4);
x_43 = lean_apply_2(x_6, x_41, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
if (x_4 == 0)
{
lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_45 = lean_apply_2(x_10, x_2, lean_box(0));
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_2);
lean_dec(x_10);
x_46 = lean_box(x_4);
x_47 = lean_apply_4(x_7, x_1, x_46, lean_box(0), lean_box(0));
return x_47;
}
}
else
{
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_7);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_48, 0, x_3);
x_49 = lean_apply_2(x_10, x_48, lean_box(0));
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
x_50 = lean_box(x_4);
x_51 = lean_apply_4(x_7, x_1, x_50, lean_box(0), lean_box(0));
return x_51;
}
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
if (x_3 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_1);
x_52 = lean_box(x_4);
x_53 = lean_apply_2(x_6, x_2, x_52);
return x_53;
}
else
{
lean_dec(x_6);
if (x_4 == 0)
{
lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_1);
x_54 = lean_apply_2(x_10, x_2, lean_box(0));
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_55 = lean_box(x_4);
x_56 = lean_box(x_4);
x_57 = lean_apply_12(x_13, x_1, x_2, x_55, x_56, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_57;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_58; 
lean_dec(x_13);
x_58 = lean_ctor_get_uint8(x_2, 0);
if (x_58 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
if (x_3 == 0)
{
uint8_t x_59; 
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
if (x_4 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_2);
lean_dec(x_12);
x_60 = lean_box(x_4);
x_61 = lean_apply_4(x_8, x_1, x_60, lean_box(0), lean_box(0));
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set_uint8(x_2, 0, x_4);
x_62 = lean_apply_2(x_12, x_2, lean_box(0));
return x_62;
}
}
else
{
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
x_63 = lean_box(x_4);
x_64 = lean_apply_4(x_8, x_1, x_63, lean_box(0), lean_box(0));
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_65, 0, x_4);
x_66 = lean_apply_2(x_12, x_65, lean_box(0));
return x_66;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
if (x_4 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_68 = lean_box(x_4);
x_69 = lean_apply_2(x_5, x_2, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_70 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_70, 0, x_4);
x_71 = lean_box(x_4);
x_72 = lean_apply_2(x_5, x_70, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_box(x_4);
x_74 = lean_apply_2(x_5, x_2, x_73);
return x_74;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_75; 
lean_dec(x_7);
x_75 = lean_apply_2(x_9, x_2, lean_box(0));
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_2);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_77 = lean_box(x_3);
x_78 = lean_apply_4(x_7, x_2, x_77, lean_box(0), lean_box(0));
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_79 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_79, 0, x_4);
x_80 = lean_box(x_3);
x_81 = lean_apply_4(x_7, x_79, x_80, lean_box(0), lean_box(0));
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
lean_dec(x_7);
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
if (x_4 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_ctor_set_uint8(x_2, 0, x_3);
x_83 = lean_box(x_4);
x_84 = lean_apply_2(x_5, x_2, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_ctor_set_uint8(x_2, 0, x_4);
x_85 = lean_box(x_4);
x_86 = lean_apply_2(x_5, x_2, x_85);
return x_86;
}
}
else
{
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_87, 0, x_3);
x_88 = lean_box(x_4);
x_89 = lean_apply_2(x_5, x_87, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_90, 0, x_4);
x_91 = lean_box(x_4);
x_92 = lean_apply_2(x_5, x_90, x_91);
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_93 = !lean_is_exclusive(x_1);
if (x_93 == 0)
{
if (x_3 == 0)
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_94; 
lean_free_object(x_1);
lean_dec(x_13);
x_94 = lean_apply_2(x_9, x_2, lean_box(0));
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
lean_ctor_set_uint8(x_1, 0, x_4);
x_95 = lean_box(x_3);
x_96 = lean_box(x_4);
x_97 = lean_apply_12(x_13, x_1, x_2, x_95, x_96, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_9);
x_98 = lean_box(x_4);
x_99 = lean_apply_2(x_5, x_2, x_98);
return x_99;
}
}
else
{
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_100; 
lean_dec(x_13);
x_100 = lean_apply_2(x_9, x_2, lean_box(0));
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
x_101 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_101, 0, x_4);
x_102 = lean_box(x_3);
x_103 = lean_box(x_4);
x_104 = lean_apply_12(x_13, x_101, x_2, x_102, x_103, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_13);
lean_dec(x_9);
x_105 = lean_box(x_4);
x_106 = lean_apply_2(x_5, x_2, x_105);
return x_106;
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_2, 0);
if (x_107 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
if (x_3 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_12);
x_108 = lean_box(x_4);
x_109 = lean_apply_4(x_8, x_1, x_108, lean_box(0), lean_box(0));
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_8);
x_110 = lean_apply_2(x_12, x_1, lean_box(0));
return x_110;
}
}
else
{
lean_dec(x_12);
if (x_4 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_13);
lean_dec(x_2);
x_111 = lean_box(x_3);
x_112 = lean_apply_4(x_8, x_1, x_111, lean_box(0), lean_box(0));
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_8);
x_113 = lean_box(x_4);
x_114 = lean_box(x_4);
x_115 = lean_apply_12(x_13, x_1, x_2, x_113, x_114, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_12);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
if (x_3 == 0)
{
lean_free_object(x_2);
lean_dec(x_13);
if (x_4 == 0)
{
lean_object* x_117; 
lean_dec(x_7);
x_117 = lean_apply_3(x_11, x_1, lean_box(0), lean_box(0));
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
x_118 = lean_box(x_3);
x_119 = lean_apply_4(x_7, x_1, x_118, lean_box(0), lean_box(0));
return x_119;
}
}
else
{
lean_dec(x_11);
if (x_4 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_7);
lean_ctor_set_uint8(x_2, 0, x_3);
x_120 = lean_box(x_3);
x_121 = lean_box(x_4);
x_122 = lean_apply_12(x_13, x_1, x_2, x_120, x_121, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_free_object(x_2);
lean_dec(x_13);
x_123 = lean_box(x_4);
x_124 = lean_apply_4(x_7, x_1, x_123, lean_box(0), lean_box(0));
return x_124;
}
}
}
else
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_dec(x_13);
if (x_4 == 0)
{
lean_object* x_125; 
lean_dec(x_7);
x_125 = lean_apply_3(x_11, x_1, lean_box(0), lean_box(0));
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_11);
x_126 = lean_box(x_3);
x_127 = lean_apply_4(x_7, x_1, x_126, lean_box(0), lean_box(0));
return x_127;
}
}
else
{
lean_dec(x_11);
if (x_4 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_7);
x_128 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_128, 0, x_3);
x_129 = lean_box(x_3);
x_130 = lean_box(x_4);
x_131 = lean_apply_12(x_13, x_1, x_128, x_129, x_130, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_13);
x_132 = lean_box(x_4);
x_133 = lean_apply_4(x_7, x_1, x_132, lean_box(0), lean_box(0));
return x_133;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_134 = lean_box(x_3);
x_135 = lean_box(x_4);
x_136 = lean_apply_12(x_13, x_1, x_2, x_134, x_135, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_136;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___rarg(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_4(x_3, x_4, x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__2_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Cached(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
