// Lean compiler output
// Module: Lean.Meta.CollectFVars
// Imports: public import Lean.Util.CollectFVars public import Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_removeUnused___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_st_ref_take(x_2);
x_12 = l_Lean_collectFVars(x_11, x_10);
x_13 = lean_st_ref_set(x_2, x_12);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_st_ref_take(x_2);
x_17 = l_Lean_collectFVars(x_16, x_15);
x_18 = lean_st_ref_set(x_2, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___Lean_Expr_collectFVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_8 = l_Lean_Expr_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Expr_collectFVars(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Expr_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_12);
x_13 = l_Lean_Expr_collectFVars(x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalDecl_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_st_ref_get(x_1);
x_6 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_st_ref_take(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_st_ref_set(x_1, x_13);
x_15 = lean_array_fget(x_6, x_5);
lean_dec(x_5);
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_getNext_x3f___redArg(x_1, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_3);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_13);
x_14 = lean_local_ctx_find(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_3);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_LocalDecl_collectFVars(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_17);
goto _start;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_23);
x_24 = lean_local_ctx_find(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = l_Lean_LocalDecl_collectFVars(x_27, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_28);
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
x_8 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_mk_ref(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_st_mk_ref(x_8);
x_10 = l___private_Lean_Meta_CollectFVars_0__Lean_CollectFVars_State_addDependencies_go(x_9, x_7, x_2, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_13);
x_14 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_15 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_15);
x_16 = lean_st_ref_get(x_7);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_addDependencies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_CollectFVars_State_addDependencies(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_33 = lean_infer_type(x_24, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_st_mk_ref(x_14);
x_36 = l_Lean_Expr_collectFVars(x_34, x_35, x_5, x_6, x_7, x_8);
lean_dec_ref(x_36);
x_37 = lean_st_ref_get(x_35);
lean_dec(x_35);
x_38 = lean_array_push(x_20, x_24);
lean_ctor_set(x_12, 1, x_37);
lean_ctor_set(x_12, 0, x_38);
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_43 = lean_infer_type(x_24, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_st_mk_ref(x_14);
x_46 = l_Lean_Expr_collectFVars(x_44, x_45, x_5, x_6, x_7, x_8);
lean_dec_ref(x_46);
x_47 = lean_st_ref_get(x_45);
lean_dec(x_45);
x_48 = lean_array_push(x_20, x_24);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_11, 1, x_49);
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_11, 0);
lean_inc(x_54);
lean_dec(x_11);
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_14, 1);
x_57 = 1;
x_58 = lean_usize_sub(x_2, x_57);
x_59 = lean_array_uget(x_1, x_58);
x_60 = l_Lean_Expr_fvarId_x21(x_59);
x_61 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_60, x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_59);
lean_inc(x_60);
x_62 = lean_local_ctx_erase(x_15, x_60);
x_63 = l_Lean_LocalInstances_erase(x_54, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_4, 1, x_64);
lean_ctor_set(x_4, 0, x_62);
x_2 = x_58;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_inc(x_55);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_66 = x_12;
} else {
 lean_dec_ref(x_12);
 x_66 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_59);
x_67 = lean_infer_type(x_59, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_st_mk_ref(x_14);
x_70 = l_Lean_Expr_collectFVars(x_68, x_69, x_5, x_6, x_7, x_8);
lean_dec_ref(x_70);
x_71 = lean_st_ref_get(x_69);
lean_dec(x_69);
x_72 = lean_array_push(x_55, x_59);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_4, 1, x_74);
x_2 = x_58;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_79 = lean_ctor_get(x_12, 1);
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = lean_ctor_get(x_11, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_82 = x_11;
} else {
 lean_dec_ref(x_11);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_12, 0);
x_84 = lean_ctor_get(x_79, 1);
x_85 = 1;
x_86 = lean_usize_sub(x_2, x_85);
x_87 = lean_array_uget(x_1, x_86);
x_88 = l_Lean_Expr_fvarId_x21(x_87);
x_89 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_88, x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_87);
lean_inc(x_88);
x_90 = lean_local_ctx_erase(x_80, x_88);
x_91 = l_Lean_LocalInstances_erase(x_81, x_88);
if (lean_is_scalar(x_82)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_82;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_12);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_2 = x_86;
x_4 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_inc(x_83);
lean_inc(x_79);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_95 = x_12;
} else {
 lean_dec_ref(x_12);
 x_95 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_87);
x_96 = lean_infer_type(x_87, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = lean_st_mk_ref(x_79);
x_99 = l_Lean_Expr_collectFVars(x_97, x_98, x_5, x_6, x_7, x_8);
lean_dec_ref(x_99);
x_100 = lean_st_ref_get(x_98);
lean_dec(x_98);
x_101 = lean_array_push(x_83, x_87);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
if (lean_is_scalar(x_82)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_82;
}
lean_ctor_set(x_103, 0, x_81);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_80);
lean_ctor_set(x_104, 1, x_103);
x_2 = x_86;
x_4 = x_104;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_95);
lean_dec_ref(x_87);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_107 = x_96;
} else {
 lean_dec_ref(x_96);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_4);
return x_109;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_33 = lean_infer_type(x_24, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_st_mk_ref(x_14);
x_36 = l_Lean_Expr_collectFVars(x_34, x_35, x_5, x_6, x_7, x_8);
lean_dec_ref(x_36);
x_37 = lean_st_ref_get(x_35);
lean_dec(x_35);
x_38 = lean_array_push(x_20, x_24);
lean_ctor_set(x_12, 1, x_37);
lean_ctor_set(x_12, 0, x_38);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
return x_39;
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_24);
x_43 = lean_infer_type(x_24, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_st_mk_ref(x_14);
x_46 = l_Lean_Expr_collectFVars(x_44, x_45, x_5, x_6, x_7, x_8);
lean_dec_ref(x_46);
x_47 = lean_st_ref_get(x_45);
lean_dec(x_45);
x_48 = lean_array_push(x_20, x_24);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_11, 1, x_49);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_11, 0);
lean_inc(x_54);
lean_dec(x_11);
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_14, 1);
x_57 = 1;
x_58 = lean_usize_sub(x_2, x_57);
x_59 = lean_array_uget(x_1, x_58);
x_60 = l_Lean_Expr_fvarId_x21(x_59);
x_61 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_60, x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_59);
lean_inc(x_60);
x_62 = lean_local_ctx_erase(x_15, x_60);
x_63 = l_Lean_LocalInstances_erase(x_54, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_4, 1, x_64);
lean_ctor_set(x_4, 0, x_62);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_58, x_3, x_4, x_5, x_6, x_7, x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_inc(x_55);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_66 = x_12;
} else {
 lean_dec_ref(x_12);
 x_66 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_59);
x_67 = lean_infer_type(x_59, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_st_mk_ref(x_14);
x_70 = l_Lean_Expr_collectFVars(x_68, x_69, x_5, x_6, x_7, x_8);
lean_dec_ref(x_70);
x_71 = lean_st_ref_get(x_69);
lean_dec(x_69);
x_72 = lean_array_push(x_55, x_59);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_4, 1, x_74);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_58, x_3, x_4, x_5, x_6, x_7, x_8);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_79 = lean_ctor_get(x_12, 1);
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = lean_ctor_get(x_11, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_82 = x_11;
} else {
 lean_dec_ref(x_11);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_12, 0);
x_84 = lean_ctor_get(x_79, 1);
x_85 = 1;
x_86 = lean_usize_sub(x_2, x_85);
x_87 = lean_array_uget(x_1, x_86);
x_88 = l_Lean_Expr_fvarId_x21(x_87);
x_89 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_removeUnused_spec__0___redArg(x_88, x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_87);
lean_inc(x_88);
x_90 = lean_local_ctx_erase(x_80, x_88);
x_91 = l_Lean_LocalInstances_erase(x_81, x_88);
if (lean_is_scalar(x_82)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_82;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_12);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_86, x_3, x_93, x_5, x_6, x_7, x_8);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_inc(x_83);
lean_inc(x_79);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_95 = x_12;
} else {
 lean_dec_ref(x_12);
 x_95 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_87);
x_96 = lean_infer_type(x_87, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = lean_st_mk_ref(x_79);
x_99 = l_Lean_Expr_collectFVars(x_97, x_98, x_5, x_6, x_7, x_8);
lean_dec_ref(x_99);
x_100 = lean_st_ref_get(x_98);
lean_dec(x_98);
x_101 = lean_array_push(x_83, x_87);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
if (lean_is_scalar(x_82)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_82;
}
lean_ctor_set(x_103, 0, x_81);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_80);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_86, x_3, x_104, x_5, x_6, x_7, x_8);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_95);
lean_dec_ref(x_87);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_107 = x_96;
} else {
 lean_dec_ref(x_96);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_4);
return x_109;
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
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; 
x_17 = l_Lean_Meta_getLocalInstances___redArg(x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Meta_removeUnused___closed__0;
x_22 = lean_array_get_size(x_1);
x_23 = lean_nat_dec_lt(x_20, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_inc_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = x_19;
x_9 = x_18;
x_10 = x_21;
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_inc_ref(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = 0;
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(x_1, x_27, x_28, x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_8 = x_33;
x_9 = x_34;
x_10 = x_35;
x_11 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
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
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Meta_removeUnused_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_removeUnused___closed__0 = _init_l_Lean_Meta_removeUnused___closed__0();
lean_mark_persistent(l_Lean_Meta_removeUnused___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
