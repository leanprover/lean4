// Lean compiler output
// Module: Lean.Meta.CollectFVars
// Imports: Lean.Util.CollectFVars Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_removeUnused___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_collectFVars(x_12, x_9);
x_15 = lean_st_ref_set(x_2, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Expr_collectFVars(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Expr_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_11);
lean_dec(x_5);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_lt(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_11);
lean_dec(x_9);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_7);
x_15 = lean_st_ref_take(x_1, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_16, x_18);
lean_dec(x_16);
x_20 = lean_st_ref_set(x_1, x_19, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_11, x_9);
lean_dec(x_9);
lean_dec_ref(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_array_fget(x_11, x_9);
lean_dec(x_9);
lean_dec_ref(x_11);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_31);
lean_dec(x_5);
x_32 = lean_array_get_size(x_31);
x_33 = lean_nat_dec_lt(x_29, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_31);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_st_ref_take(x_1, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_37, x_39);
lean_dec(x_37);
x_41 = lean_st_ref_set(x_1, x_40, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_array_fget(x_31, x_29);
lean_dec(x_29);
lean_dec_ref(x_31);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_3);
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
lean_dec_ref(x_9);
x_20 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_20);
x_21 = lean_local_ctx_find(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_3);
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
lean_dec_ref(x_21);
x_24 = l_Lean_LocalDecl_collectFVars(x_23, x_2, x_3, x_4, x_5, x_6, x_17);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
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
lean_dec_ref(x_9);
x_29 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_29);
x_30 = lean_local_ctx_find(x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_3);
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
lean_dec_ref(x_30);
x_34 = l_Lean_LocalDecl_collectFVars(x_33, x_2, x_3, x_4, x_5, x_6, x_27);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_7 = x_35;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(x_12, x_8, x_2, x_3, x_4, x_5, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_st_ref_get(x_8, x_17);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_CollectFVars_State_addDependencies(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_14, 1);
x_22 = 1;
x_23 = lean_usize_sub(x_2, x_22);
x_24 = lean_array_uget(x_1, x_23);
x_25 = l_Lean_Expr_fvarId_x21(x_24);
x_26 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_25, x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_24);
lean_inc(x_25);
x_27 = lean_local_ctx_erase(x_15, x_25);
x_28 = l_Lean_LocalInstances_erase(x_18, x_25);
lean_ctor_set(x_11, 0, x_28);
lean_ctor_set(x_4, 0, x_27);
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
lean_inc(x_20);
lean_inc(x_14);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_33 = lean_infer_type(x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_mk_ref(x_14, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Expr_collectFVars(x_34, x_37, x_5, x_6, x_7, x_8, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_st_ref_get(x_37, x_40);
lean_dec(x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_array_push(x_20, x_24);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_44);
x_2 = x_23;
x_9 = x_43;
goto _start;
}
else
{
uint8_t x_46; 
lean_free_object(x_12);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_free_object(x_11);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_50 = lean_infer_type(x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_st_mk_ref(x_14, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Expr_collectFVars(x_51, x_54, x_5, x_6, x_7, x_8, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_st_ref_get(x_54, x_57);
lean_dec(x_54);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_array_push(x_20, x_24);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_11, 1, x_62);
x_2 = x_23;
x_9 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_24);
lean_dec(x_20);
lean_free_object(x_11);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_14, 1);
x_71 = 1;
x_72 = lean_usize_sub(x_2, x_71);
x_73 = lean_array_uget(x_1, x_72);
x_74 = l_Lean_Expr_fvarId_x21(x_73);
x_75 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_74, x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_73);
lean_inc(x_74);
x_76 = lean_local_ctx_erase(x_15, x_74);
x_77 = l_Lean_LocalInstances_erase(x_68, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_12);
lean_ctor_set(x_4, 1, x_78);
lean_ctor_set(x_4, 0, x_76);
x_2 = x_72;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_inc(x_69);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_80 = x_12;
} else {
 lean_dec_ref(x_12);
 x_80 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_73);
x_81 = lean_infer_type(x_73, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_st_mk_ref(x_14, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_Lean_Expr_collectFVars(x_82, x_85, x_5, x_6, x_7, x_8, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_st_ref_get(x_85, x_88);
lean_dec(x_85);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = lean_array_push(x_69, x_73);
if (lean_is_scalar(x_80)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_80;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_68);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_4, 1, x_94);
x_2 = x_72;
x_9 = x_91;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_80);
lean_dec_ref(x_73);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_98 = x_81;
} else {
 lean_dec_ref(x_81);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_12, 1);
x_101 = lean_ctor_get(x_4, 0);
lean_inc(x_101);
lean_dec(x_4);
x_102 = lean_ctor_get(x_11, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_103 = x_11;
} else {
 lean_dec_ref(x_11);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_12, 0);
x_105 = lean_ctor_get(x_100, 1);
x_106 = 1;
x_107 = lean_usize_sub(x_2, x_106);
x_108 = lean_array_uget(x_1, x_107);
x_109 = l_Lean_Expr_fvarId_x21(x_108);
x_110 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_109, x_105);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_108);
lean_inc(x_109);
x_111 = lean_local_ctx_erase(x_101, x_109);
x_112 = l_Lean_LocalInstances_erase(x_102, x_109);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_12);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_2 = x_107;
x_4 = x_114;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_109);
lean_inc(x_104);
lean_inc(x_100);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_116 = x_12;
} else {
 lean_dec_ref(x_12);
 x_116 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_108);
x_117 = lean_infer_type(x_108, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_st_mk_ref(x_100, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_Expr_collectFVars(x_118, x_121, x_5, x_6, x_7, x_8, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_st_ref_get(x_121, x_124);
lean_dec(x_121);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_array_push(x_104, x_108);
if (lean_is_scalar(x_116)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_116;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_103)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_103;
}
lean_ctor_set(x_130, 0, x_102);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_101);
lean_ctor_set(x_131, 1, x_130);
x_2 = x_107;
x_4 = x_131;
x_9 = x_127;
goto _start;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_116);
lean_dec_ref(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = lean_ctor_get(x_117, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_135 = x_117;
} else {
 lean_dec_ref(x_117);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_9);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_14, 1);
x_22 = 1;
x_23 = lean_usize_sub(x_2, x_22);
x_24 = lean_array_uget(x_1, x_23);
x_25 = l_Lean_Expr_fvarId_x21(x_24);
x_26 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_25, x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_24);
lean_inc(x_25);
x_27 = lean_local_ctx_erase(x_15, x_25);
x_28 = l_Lean_LocalInstances_erase(x_18, x_25);
lean_ctor_set(x_11, 0, x_28);
lean_ctor_set(x_4, 0, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
lean_inc(x_20);
lean_inc(x_14);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_33 = lean_infer_type(x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_mk_ref(x_14, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Expr_collectFVars(x_34, x_37, x_5, x_6, x_7, x_8, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_st_ref_get(x_37, x_40);
lean_dec(x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_array_push(x_20, x_24);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_44);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_45;
}
else
{
uint8_t x_46; 
lean_free_object(x_12);
lean_dec_ref(x_24);
lean_dec(x_20);
lean_free_object(x_11);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_50 = lean_infer_type(x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_st_mk_ref(x_14, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Expr_collectFVars(x_51, x_54, x_5, x_6, x_7, x_8, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_st_ref_get(x_54, x_57);
lean_dec(x_54);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_array_push(x_20, x_24);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_11, 1, x_62);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_24);
lean_dec(x_20);
lean_free_object(x_11);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_14, 1);
x_71 = 1;
x_72 = lean_usize_sub(x_2, x_71);
x_73 = lean_array_uget(x_1, x_72);
x_74 = l_Lean_Expr_fvarId_x21(x_73);
x_75 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_74, x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_73);
lean_inc(x_74);
x_76 = lean_local_ctx_erase(x_15, x_74);
x_77 = l_Lean_LocalInstances_erase(x_68, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_12);
lean_ctor_set(x_4, 1, x_78);
lean_ctor_set(x_4, 0, x_76);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_inc(x_69);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_80 = x_12;
} else {
 lean_dec_ref(x_12);
 x_80 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_73);
x_81 = lean_infer_type(x_73, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_st_mk_ref(x_14, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_Lean_Expr_collectFVars(x_82, x_85, x_5, x_6, x_7, x_8, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_st_ref_get(x_85, x_88);
lean_dec(x_85);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = lean_array_push(x_69, x_73);
if (lean_is_scalar(x_80)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_80;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_68);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_4, 1, x_94);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_80);
lean_dec_ref(x_73);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_98 = x_81;
} else {
 lean_dec_ref(x_81);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_12, 1);
x_101 = lean_ctor_get(x_4, 0);
lean_inc(x_101);
lean_dec(x_4);
x_102 = lean_ctor_get(x_11, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_103 = x_11;
} else {
 lean_dec_ref(x_11);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_12, 0);
x_105 = lean_ctor_get(x_100, 1);
x_106 = 1;
x_107 = lean_usize_sub(x_2, x_106);
x_108 = lean_array_uget(x_1, x_107);
x_109 = l_Lean_Expr_fvarId_x21(x_108);
x_110 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_109, x_105);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_108);
lean_inc(x_109);
x_111 = lean_local_ctx_erase(x_101, x_109);
x_112 = l_Lean_LocalInstances_erase(x_102, x_109);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_12);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_107, x_3, x_114, x_5, x_6, x_7, x_8, x_9);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_109);
lean_inc(x_104);
lean_inc(x_100);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_116 = x_12;
} else {
 lean_dec_ref(x_12);
 x_116 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_108);
x_117 = lean_infer_type(x_108, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_st_mk_ref(x_100, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_Expr_collectFVars(x_118, x_121, x_5, x_6, x_7, x_8, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_st_ref_get(x_121, x_124);
lean_dec(x_121);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_array_push(x_104, x_108);
if (lean_is_scalar(x_116)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_116;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_103)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_103;
}
lean_ctor_set(x_130, 0, x_102);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_101);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_107, x_3, x_131, x_5, x_6, x_7, x_8, x_127);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_116);
lean_dec_ref(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = lean_ctor_get(x_117, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_135 = x_117;
} else {
 lean_dec_ref(x_117);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_9);
return x_137;
}
}
}
static lean_object* _init_l_Lean_Meta_removeUnused___closed__0() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; 
x_17 = l_Lean_Meta_getLocalInstances___redArg(x_3, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Meta_removeUnused___closed__0;
x_23 = lean_array_get_size(x_1);
x_24 = lean_nat_dec_lt(x_21, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_inc_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = x_20;
x_9 = x_18;
x_10 = x_22;
x_11 = x_19;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
lean_inc_ref(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(x_1, x_28, x_29, x_27, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec_ref(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_8 = x_35;
x_9 = x_36;
x_10 = x_37;
x_11 = x_34;
goto block_16;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Array_reverse___redArg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_removeUnused___closed__0 = _init_l_Lean_Meta_removeUnused___closed__0();
lean_mark_persistent(l_Lean_Meta_removeUnused___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
