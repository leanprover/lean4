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
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignment_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedAssignment_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MetavarContext_occursCheck___closed__1;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* l_Std_HashSetImp_insert___at___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visit_match__1(lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_match__1(lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_occursCheck(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__1(lean_object*);
uint8_t l_Std_HashSetImp_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__2(lean_object*);
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_occursCheck_visitMVar_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_occursCheck_visitMVar_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_2(x_8, x_10, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_3(x_7, x_14, x_15, x_17);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_4, x_19, x_20, x_21, x_23);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_3, x_25, x_26, x_27, x_29);
return x_30;
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_5(x_5, x_31, x_32, x_33, x_34, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_41 = lean_box_uint64(x_40);
x_42 = lean_apply_3(x_6, x_38, x_39, x_41);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_4(x_2, x_43, x_44, x_45, x_47);
return x_48;
}
default: 
{
lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_apply_1(x_9, x_1);
return x_49;
}
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_occursCheck_visit_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_occursCheck_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_occursCheck_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_name_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_MetavarContext_getExprAssignment_x3f(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MetavarContext_getDelayedAssignment_x3f(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_11, x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_13, x_4);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasExprMVar(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_inc(x_3);
lean_inc(x_4);
x_8 = l_Std_HashSetImp_contains___at___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit___spec__1(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = l_Std_HashSetImp_insert___at___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit___spec__3(x_4, x_3);
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_MetavarContext_occursCheck_visitMVar(x_1, x_2, x_10, x_9);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_14 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_12, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
case 6:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_1);
x_23 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_21, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_3 = x_22;
x_4 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_1);
x_32 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_30, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_3 = x_31;
x_4 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 8:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 3);
lean_inc(x_41);
lean_dec(x_3);
lean_inc(x_1);
x_42 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_39, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_40, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_3 = x_41;
x_4 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 10:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
lean_dec(x_3);
x_3 = x_55;
x_4 = x_9;
goto _start;
}
case 11:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_dec(x_3);
x_3 = x_57;
x_4 = x_9;
goto _start;
}
default: 
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visitMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_occursCheck_visitMVar(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_occursCheck_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_MetavarContext_occursCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
uint8_t l_Lean_MetavarContext_occursCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasExprMVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_MetavarContext_occursCheck___closed__1;
x_7 = l_Lean_MetavarContext_occursCheck_visit(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_7);
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
}
}
}
lean_object* l_Lean_MetavarContext_occursCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_MetavarContext_occursCheck(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_OccursCheck(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MetavarContext_occursCheck___closed__1 = _init_l_Lean_MetavarContext_occursCheck___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_occursCheck___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
