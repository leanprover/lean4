// Lean compiler output
// Module: Lean.Util.OccursCheck
// Imports: Init Lean.MetavarContext
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
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___closed__1;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Std_HashSetImp_insert___at___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___closed__1;
lean_object* l_Lean_getExprMVarAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSetImp_contains___at___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getDelayedMVarAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_occursCheck_visitMVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_name_eq(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = l_Lean_getExprMVarAssignment_x3f(x_2, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lean_getDelayedMVarAssignment_x3f(x_2, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l_Lean_occursCheck_visitMVar___closed__1;
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 0, x_16);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_occursCheck_visitMVar___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_6);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_occursCheck_visit(x_1, x_22, x_3, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = l_Lean_getDelayedMVarAssignment_x3f(x_2, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = l_Lean_occursCheck_visitMVar___closed__1;
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_occursCheck_visit(x_1, x_34, x_3, x_32);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
lean_dec(x_7);
x_38 = l_Lean_occursCheck_visit(x_1, x_37, x_3, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_39 = l_Lean_occursCheck_visitMVar___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasExprMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = l_Lean_occursCheck_visitMVar___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_3);
x_9 = l_Std_HashSetImp_contains___at___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit___spec__1(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Std_HashSetImp_insert___at___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit___spec__3(x_3, x_2);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_occursCheck_visitMVar(x_1, x_11, x_10, x_4);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_occursCheck_visit(x_1, x_13, x_10, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_32 = x_16;
} else {
 lean_dec_ref(x_16);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_34 = x_17;
} else {
 lean_dec_ref(x_17);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
x_2 = x_14;
x_3 = x_39;
x_4 = x_38;
goto _start;
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_Lean_occursCheck_visit(x_1, x_41, x_10, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_42);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_44, 0, x_52);
return x_43;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_55 = x_45;
} else {
 lean_dec_ref(x_45);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_43, 0, x_57);
return x_43;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_60 = x_44;
} else {
 lean_dec_ref(x_44);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_45);
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
lean_dec(x_43);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
lean_dec(x_44);
x_2 = x_42;
x_3 = x_67;
x_4 = x_66;
goto _start;
}
}
case 7:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_occursCheck_visit(x_1, x_69, x_10, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_70);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_72, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_72, 0, x_80);
return x_71;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_83 = x_73;
} else {
 lean_dec_ref(x_73);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_71, 0, x_85);
return x_71;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_88 = x_72;
} else {
 lean_dec_ref(x_72);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_73);
x_94 = lean_ctor_get(x_71, 1);
lean_inc(x_94);
lean_dec(x_71);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
lean_dec(x_72);
x_2 = x_70;
x_3 = x_95;
x_4 = x_94;
goto _start;
}
}
case 8:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 3);
lean_inc(x_99);
lean_dec(x_2);
x_100 = l_Lean_occursCheck_visit(x_1, x_97, x_10, x_4);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_99);
lean_dec(x_98);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_100, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_101, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_102);
if (x_107 == 0)
{
return x_100;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
lean_dec(x_102);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_101, 0, x_109);
return x_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_112 = x_102;
} else {
 lean_dec_ref(x_102);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_100, 0, x_114);
return x_100;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
lean_dec(x_100);
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_117 = x_101;
} else {
 lean_dec_ref(x_101);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_102, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_119 = x_102;
} else {
 lean_dec_ref(x_102);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_116);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_102);
x_123 = lean_ctor_get(x_100, 1);
lean_inc(x_123);
lean_dec(x_100);
x_124 = lean_ctor_get(x_101, 1);
lean_inc(x_124);
lean_dec(x_101);
x_125 = l_Lean_occursCheck_visit(x_1, x_98, x_124, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
lean_dec(x_99);
x_128 = !lean_is_exclusive(x_125);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_125, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_126, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_127);
if (x_132 == 0)
{
return x_125;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
lean_dec(x_127);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_126, 0, x_134);
return x_125;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
lean_dec(x_126);
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_125, 0, x_139);
return x_125;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_125, 1);
lean_inc(x_140);
lean_dec(x_125);
x_141 = lean_ctor_get(x_126, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_142 = x_126;
} else {
 lean_dec_ref(x_126);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_127, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_144 = x_127;
} else {
 lean_dec_ref(x_127);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
x_148 = lean_ctor_get(x_125, 1);
lean_inc(x_148);
lean_dec(x_125);
x_149 = lean_ctor_get(x_126, 1);
lean_inc(x_149);
lean_dec(x_126);
x_2 = x_99;
x_3 = x_149;
x_4 = x_148;
goto _start;
}
}
}
case 10:
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
lean_dec(x_2);
x_2 = x_151;
x_3 = x_10;
goto _start;
}
case 11:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_2, 2);
lean_inc(x_153);
lean_dec(x_2);
x_2 = x_153;
x_3 = x_10;
goto _start;
}
default: 
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_155 = l_Lean_occursCheck_visitMVar___closed__1;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_10);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_4);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_158 = l_Lean_occursCheck_visitMVar___closed__1;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_3);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_4);
return x_160;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_occursCheck_visitMVar(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_occursCheck_visit(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_occursCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasExprMVar(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_occursCheck___closed__1;
x_9 = l_Lean_occursCheck_visit(x_1, x_2, x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_occursCheck(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_OccursCheck(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_occursCheck_visitMVar___closed__1 = _init_l_Lean_occursCheck_visitMVar___closed__1();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___closed__1);
l_Lean_occursCheck_visitMVar___closed__2 = _init_l_Lean_occursCheck_visitMVar___closed__2();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___closed__2);
l_Lean_occursCheck___closed__1 = _init_l_Lean_occursCheck___closed__1();
lean_mark_persistent(l_Lean_occursCheck___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
