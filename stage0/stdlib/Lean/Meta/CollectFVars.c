// Lean compiler output
// Module: Lean.Meta.CollectFVars
// Imports: Init Lean.Util.CollectFVars Lean.Meta.Basic
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
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2;
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6;
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5;
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_removeUnused___closed__1;
static lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVarsCore(x_15, x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_6, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_18);
x_26 = lean_st_ref_set(x_4, x_22, x_23);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_22, 1);
x_32 = lean_ctor_get(x_22, 2);
x_33 = lean_ctor_get(x_22, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_23);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_CollectFVars_main(x_9, x_14);
x_17 = lean_st_ref_set(x_2, x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_Lean_Expr_collectFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Expr_collectFVars(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Expr_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_collectFVars(x_11, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalDecl_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_1, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_17);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_15);
x_23 = lean_array_fget(x_19, x_17);
lean_dec(x_17);
lean_dec(x_19);
x_24 = lean_st_ref_get(x_6, x_18);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_1, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
x_31 = lean_st_ref_set(x_1, x_30, x_28);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_23);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_ctor_get(x_11, 2);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_38, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_array_fget(x_40, x_38);
lean_dec(x_38);
lean_dec(x_40);
x_46 = lean_st_ref_get(x_6, x_39);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_1, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_49, x_51);
lean_dec(x_49);
x_53 = lean_st_ref_set(x_1, x_52, x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_45);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_CollectFVars_State_addDependencies_getNext_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_CollectFVars_State_addDependencies_getNext_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_local_ctx_find(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_8);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_collectFVars(x_23, x_2, x_3, x_4, x_5, x_6, x_17);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_7 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_local_ctx_find(x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_LocalDecl_collectFVars(x_33, x_2, x_3, x_4, x_5, x_6, x_27);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_7 = x_35;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_CollectFVars_State_addDependencies_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_CollectFVars_State_addDependencies_go(x_16, x_10, x_2, x_3, x_4, x_5, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_5, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_10, x_25);
lean_dec(x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_CollectFVars_State_addDependencies(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CollectFVars", 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("removeUnused", 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(53u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9;
x_3 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9;
x_3 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6;
x_2 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9;
x_3 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = 1;
x_12 = lean_usize_sub(x_2, x_11);
x_13 = lean_array_uget(x_1, x_12);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11;
lean_inc(x_13);
x_27 = l_Lean_Expr_fvarId_x21(x_13, x_26);
x_28 = l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13;
lean_inc(x_13);
x_30 = l_Lean_Expr_fvarId_x21(x_13, x_29);
x_31 = lean_local_ctx_erase(x_17, x_30);
x_32 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15;
x_33 = l_Lean_Expr_fvarId_x21(x_13, x_32);
x_34 = l_Lean_LocalInstances_erase(x_20, x_33);
lean_ctor_set(x_14, 0, x_34);
lean_ctor_set(x_4, 0, x_31);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_36; 
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_36 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_8, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_mk_ref(x_24, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Expr_collectFVars(x_37, x_42, x_5, x_6, x_7, x_8, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_8, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_get(x_42, x_47);
lean_dec(x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_push(x_23, x_13);
lean_ctor_set(x_15, 1, x_49);
lean_ctor_set(x_15, 0, x_51);
x_2 = x_12;
x_9 = x_50;
goto _start;
}
else
{
uint8_t x_53; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_14);
lean_dec(x_20);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
return x_36;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_36, 0);
x_55 = lean_ctor_get(x_36, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_36);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11;
lean_inc(x_13);
x_61 = l_Lean_Expr_fvarId_x21(x_13, x_60);
x_62 = l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13;
lean_inc(x_13);
x_64 = l_Lean_Expr_fvarId_x21(x_13, x_63);
x_65 = lean_local_ctx_erase(x_17, x_64);
x_66 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15;
x_67 = l_Lean_Expr_fvarId_x21(x_13, x_66);
x_68 = l_Lean_LocalInstances_erase(x_20, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_58);
lean_ctor_set(x_14, 1, x_69);
lean_ctor_set(x_14, 0, x_68);
lean_ctor_set(x_4, 0, x_65);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_71; 
lean_dec(x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_71 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_st_ref_get(x_8, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_mk_ref(x_58, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_collectFVars(x_72, x_77, x_5, x_6, x_7, x_8, x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_get(x_8, x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_get(x_77, x_82);
lean_dec(x_77);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_array_push(x_57, x_13);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_14, 1, x_87);
x_2 = x_12;
x_9 = x_85;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_14);
lean_dec(x_20);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_ctor_get(x_71, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_14, 0);
lean_inc(x_93);
lean_dec(x_14);
x_94 = lean_ctor_get(x_15, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_96 = x_15;
} else {
 lean_dec_ref(x_15);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
x_98 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11;
lean_inc(x_13);
x_99 = l_Lean_Expr_fvarId_x21(x_13, x_98);
x_100 = l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(x_97, x_99);
lean_dec(x_99);
lean_dec(x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13;
lean_inc(x_13);
x_102 = l_Lean_Expr_fvarId_x21(x_13, x_101);
x_103 = lean_local_ctx_erase(x_17, x_102);
x_104 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15;
x_105 = l_Lean_Expr_fvarId_x21(x_13, x_104);
x_106 = l_Lean_LocalInstances_erase(x_93, x_105);
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_94);
lean_ctor_set(x_107, 1, x_95);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_4, 1, x_108);
lean_ctor_set(x_4, 0, x_103);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_110; 
lean_dec(x_100);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_110 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_st_ref_get(x_8, x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_mk_ref(x_95, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Expr_collectFVars(x_111, x_116, x_5, x_6, x_7, x_8, x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_st_ref_get(x_8, x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_st_ref_get(x_116, x_121);
lean_dec(x_116);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_push(x_94, x_13);
if (lean_is_scalar(x_96)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_96;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_93);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_4, 1, x_127);
x_2 = x_12;
x_9 = x_124;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_129 = lean_ctor_get(x_110, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_110, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_131 = x_110;
} else {
 lean_dec_ref(x_110);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_133 = lean_ctor_get(x_4, 0);
lean_inc(x_133);
lean_dec(x_4);
x_134 = lean_ctor_get(x_14, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_135 = x_14;
} else {
 lean_dec_ref(x_14);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_15, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_15, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_138 = x_15;
} else {
 lean_dec_ref(x_15);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
x_140 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11;
lean_inc(x_13);
x_141 = l_Lean_Expr_fvarId_x21(x_13, x_140);
x_142 = l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(x_139, x_141);
lean_dec(x_141);
lean_dec(x_139);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13;
lean_inc(x_13);
x_144 = l_Lean_Expr_fvarId_x21(x_13, x_143);
x_145 = lean_local_ctx_erase(x_133, x_144);
x_146 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15;
x_147 = l_Lean_Expr_fvarId_x21(x_13, x_146);
x_148 = l_Lean_LocalInstances_erase(x_134, x_147);
if (lean_is_scalar(x_138)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_138;
}
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_137);
if (lean_is_scalar(x_135)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_135;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
x_2 = x_12;
x_4 = x_151;
goto _start;
}
else
{
lean_object* x_153; 
lean_dec(x_142);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_153 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_st_ref_get(x_8, x_155);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_st_mk_ref(x_137, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Expr_collectFVars(x_154, x_159, x_5, x_6, x_7, x_8, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_st_ref_get(x_8, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_get(x_159, x_164);
lean_dec(x_159);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_array_push(x_136, x_13);
if (lean_is_scalar(x_138)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_138;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
if (lean_is_scalar(x_135)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_135;
}
lean_ctor_set(x_170, 0, x_134);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_133);
lean_ctor_set(x_171, 1, x_170);
x_2 = x_12;
x_4 = x_171;
x_9 = x_167;
goto _start;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_173 = lean_ctor_get(x_153, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_175 = x_153;
} else {
 lean_dec_ref(x_153);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_4);
lean_ctor_set(x_177, 1, x_9);
return x_177;
}
}
}
static lean_object* _init_l_Lean_Meta_removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = l_Lean_Meta_getLocalInstances(x_3, x_4, x_5, x_6, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = l_Lean_Meta_removeUnused___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_get_size(x_1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = x_40;
x_9 = x_35;
goto block_32;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_45 = 0;
x_46 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2(x_1, x_44, x_45, x_40, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_8 = x_47;
x_9 = x_48;
goto block_32;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_32:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_Array_reverse___rarg(x_17);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_14);
lean_ctor_set(x_10, 0, x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Array_reverse___rarg(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
 x_27 = lean_box(0);
}
x_28 = l_Array_reverse___rarg(x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_Meta_removeUnused___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__1);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__2);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__3);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__4);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__5);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__6);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__7);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__8);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__9);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__10);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__11);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__12);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__13);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__14);
l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15 = _init_l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lean_Meta_removeUnused___spec__2___closed__15);
l_Lean_Meta_removeUnused___closed__1 = _init_l_Lean_Meta_removeUnused___closed__1();
lean_mark_persistent(l_Lean_Meta_removeUnused___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
