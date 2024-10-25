// Lean compiler output
// Module: Lean.Compiler.IR.Sorry
// Imports: Lean.Compiler.IR.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_updateSorryDep___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sorryAx", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_IR_findDecl(x_1, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_name_eq(x_32, x_5);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_1);
lean_ctor_set_tag(x_20, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; 
lean_dec(x_32);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_9, 0, x_35);
return x_9;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_name_eq(x_36, x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_9, 0, x_41);
return x_9;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_44 = x_20;
} else {
 lean_dec_ref(x_20);
 x_44 = lean_box(0);
}
x_45 = lean_name_eq(x_43, x_5);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_44;
 lean_ctor_set_tag(x_46, 0);
}
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_44;
 lean_ctor_set_tag(x_49, 0);
}
lean_ctor_set(x_49, 0, x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
lean_dec(x_53);
x_54 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_9, 0, x_55);
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_dec(x_9);
x_57 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_name_eq(x_61, x_5);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
lean_ctor_set_tag(x_8, 0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_8);
lean_ctor_set(x_63, 1, x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_8);
lean_ctor_set(x_65, 1, x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_4);
return x_66;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_8, 0);
lean_inc(x_67);
lean_dec(x_8);
x_68 = lean_name_eq(x_67, x_5);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_2);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_4);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_4);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(x_19, x_2, x_3, x_4);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(x_21, x_2, x_3, x_4);
return x_22;
}
case 10:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
case 11:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
case 12:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_37 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitExpr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Sorry_visitFndBody(x_10, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_23 = x_13;
} else {
 lean_dec_ref(x_13);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_28 = x_12;
} else {
 lean_dec_ref(x_12);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_30 = x_13;
} else {
 lean_dec_ref(x_13);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 1;
x_38 = lean_usize_add(x_2, x_37);
x_2 = x_38;
x_4 = x_36;
x_5 = x_35;
x_7 = x_34;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_Sorry_visitExpr(x_5, x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_19 = x_9;
} else {
 lean_dec_ref(x_9);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_24 = x_8;
} else {
 lean_dec_ref(x_8);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_26 = x_9;
} else {
 lean_dec_ref(x_9);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_1 = x_6;
x_2 = x_31;
x_4 = x_30;
goto _start;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_IR_Sorry_visitFndBody(x_33, x_2, x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_36, 0, x_44);
return x_35;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_35, 0, x_49);
return x_35;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_dec(x_35);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_52 = x_36;
} else {
 lean_dec_ref(x_36);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_54 = x_37;
} else {
 lean_dec_ref(x_37);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec(x_35);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
lean_dec(x_36);
x_1 = x_34;
x_2 = x_59;
x_4 = x_58;
goto _start;
}
}
case 8:
{
uint8_t x_61; 
x_61 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_62;
goto _start;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_1, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_1, 0);
lean_dec(x_66);
x_67 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_4);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_69 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_2);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
}
}
case 9:
{
uint8_t x_72; 
x_72 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_73;
goto _start;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_1, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_1, 0);
lean_dec(x_77);
x_78 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_4);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_1);
x_80 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_array_get_size(x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_84);
lean_dec(x_83);
x_87 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_2);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_84, x_84);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_84);
lean_dec(x_83);
x_91 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_4);
return x_93;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_96 = lean_box(0);
x_97 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1(x_83, x_94, x_95, x_96, x_2, x_3, x_4);
lean_dec(x_83);
return x_97;
}
}
}
case 12:
{
uint8_t x_98; 
x_98 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_99;
goto _start;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_1, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_1, 0);
lean_dec(x_103);
x_104 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_104);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_4);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_1);
x_106 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_4);
return x_108;
}
}
}
default: 
{
uint8_t x_109; 
x_109 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_110;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_1);
x_112 = l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_4);
return x_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_visitFndBody___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFndBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitFndBody(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_IR_Sorry_visitFndBody(x_6, x_2, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_18, x_5, x_17);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_box(0);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_25, x_5, x_24);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_35, x_5, x_34);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_33;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_9, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_10, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_10, 0, x_46);
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_dec(x_10);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_9, 0, x_49);
return x_9;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_52 = x_10;
} else {
 lean_dec_ref(x_10);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_4);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_visitDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_IR_Sorry_visitDecl(x_9, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_5 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_6);
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1(x_1, x_17, x_18, x_19, x_2, x_3, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
lean_ctor_set(x_21, 0, x_19);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
lean_ctor_set(x_21, 0, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_free_object(x_21);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_2 = x_23;
x_4 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_35 = x_20;
} else {
 lean_dec_ref(x_20);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_32);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_2 = x_32;
x_4 = x_38;
goto _start;
}
}
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = 0;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_43, x_43);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_43);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1(x_1, x_53, x_54, x_55, x_42, x_3, x_4);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get_uint8(x_58, sizeof(void*)*1);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_58);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_59);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_2 = x_58;
x_4 = x_65;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Sorry_collect___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Sorry_collect(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_15, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_6, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_6, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_6, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_6, 4, x_16);
x_26 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_6, 4, x_29);
x_30 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_35, 2, x_13);
lean_ctor_set(x_35, 3, x_14);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_array_uset(x_8, x_3, x_35);
x_3 = x_10;
x_4 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_38;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_updateSorryDep___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_IR_updateSorryDep___closed__1;
x_5 = l_Lean_IR_Sorry_collect(x_1, x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1(x_8, x_9, x_10, x_1);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_1);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1(x_14, x_15, x_16, x_1);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_updateSorryDep___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_updateSorryDep(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__1);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__2);
l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3 = _init_l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3();
lean_mark_persistent(l_Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___closed__3);
l_Lean_IR_updateSorryDep___closed__1 = _init_l_Lean_IR_updateSorryDep___closed__1();
lean_mark_persistent(l_Lean_IR_updateSorryDep___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
