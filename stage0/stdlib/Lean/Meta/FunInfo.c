// Lean compiler output
// Module: Lean.Meta.FunInfo
// Imports: Init Lean.Meta.Basic Lean.Meta.InferType
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
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__2(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object*, lean_object*, size_t, size_t);
extern lean_object* l_Lean_Expr_instInhabitedExpr;
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Position_lt___closed__2;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_6, 5);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_Meta_TransparencyMode_beq(x_10, x_13);
x_17 = lean_expr_eqv(x_11, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_19;
goto _start;
}
else
{
if (x_17 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_27;
goto _start;
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_4, x_29);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_30;
goto _start;
}
else
{
if (x_16 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_4, x_32);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_15);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_4, x_39);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_40;
goto _start;
}
else
{
if (x_17 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_15);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_4, x_42);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_43;
goto _start;
}
else
{
lean_object* x_45; 
x_45 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
lean_ctor_set(x_15, 0, x_45);
return x_15;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_4, x_49);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_50;
goto _start;
}
else
{
if (x_17 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_4, x_52);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_53;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Lean_Meta_TransparencyMode_beq(x_13, x_16);
x_20 = lean_expr_eqv(x_14, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
if (x_19 == 0)
{
lean_object* x_21; 
lean_dec(x_12);
x_21 = lean_box(0);
return x_21;
}
else
{
if (x_20 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_12);
x_24 = lean_box(0);
return x_24;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_25; 
lean_dec(x_12);
x_25 = lean_box(0);
return x_25;
}
else
{
if (x_19 == 0)
{
lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_12);
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_18);
lean_dec(x_12);
x_31 = lean_box(0);
return x_31;
}
else
{
if (x_20 == 0)
{
lean_object* x_32; 
lean_free_object(x_18);
lean_dec(x_12);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_12);
x_36 = lean_box(0);
return x_36;
}
else
{
if (x_20 == 0)
{
lean_object* x_37; 
lean_dec(x_12);
x_37 = lean_box(0);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_12);
return x_38;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_39; size_t x_40; 
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
lean_dec(x_10);
x_40 = x_2 >> x_5;
x_1 = x_39;
x_2 = x_40;
goto _start;
}
default: 
{
lean_object* x_42; 
x_42 = lean_box(0);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_43, x_44, lean_box(0), x_45, x_3);
lean_dec(x_44);
lean_dec(x_43);
return x_46;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_TransparencyMode_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
if (lean_obj_tag(x_6) == 0)
{
size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = 11;
x_10 = lean_usize_mix_hash(x_8, x_9);
x_11 = lean_usize_mix_hash(x_7, x_10);
x_12 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_3, x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_usize_of_nat(x_13);
x_15 = 13;
x_16 = lean_usize_mix_hash(x_14, x_15);
x_17 = lean_usize_mix_hash(x_8, x_16);
x_18 = lean_usize_mix_hash(x_7, x_17);
x_19 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_3, x_18, x_2);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = x_1 - x_11;
x_13 = 5;
x_14 = x_13 * x_12;
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = l_Lean_Meta_TransparencyMode_hash(x_17);
x_21 = l_Lean_Expr_hash(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = 11;
x_23 = lean_usize_mix_hash(x_21, x_22);
x_24 = lean_usize_mix_hash(x_20, x_23);
x_25 = x_24 >> x_14;
x_26 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_6, x_25, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_26;
goto _start;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 13;
x_31 = lean_usize_mix_hash(x_29, x_30);
x_32 = lean_usize_mix_hash(x_21, x_31);
x_33 = lean_usize_mix_hash(x_20, x_32);
x_34 = x_33 >> x_14;
x_35 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_6, x_34, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_35;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_array_fget(x_5, x_2);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Meta_TransparencyMode_beq(x_23, x_26);
x_30 = lean_expr_eqv(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_2, x_31);
lean_dec(x_2);
x_2 = x_32;
goto _start;
}
else
{
if (x_30 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_box(0);
x_17 = x_37;
goto block_21;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
lean_dec(x_2);
x_2 = x_39;
goto _start;
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_2, x_41);
lean_dec(x_2);
x_2 = x_42;
goto _start;
}
else
{
if (x_29 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
lean_dec(x_2);
x_2 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_ctor_get(x_28, 0);
lean_inc(x_48);
lean_dec(x_28);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_6);
lean_dec(x_5);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_2, x_50);
lean_dec(x_2);
x_2 = x_51;
goto _start;
}
else
{
if (x_30 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_2, x_53);
lean_dec(x_2);
x_2 = x_54;
goto _start;
}
else
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = lean_box(0);
x_17 = x_56;
goto block_21;
}
}
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = lean_array_fset(x_5, x_2, x_3);
x_19 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_7;
}
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_6, x_12);
x_17 = lean_box(2);
x_18 = lean_array_fset(x_6, x_12, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
x_34 = l_Lean_Meta_TransparencyMode_beq(x_28, x_31);
x_35 = lean_expr_eqv(x_29, x_32);
lean_dec(x_32);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
if (lean_obj_tag(x_33) == 0)
{
if (x_34 == 0)
{
lean_object* x_36; 
lean_free_object(x_16);
x_36 = lean_box(0);
x_22 = x_36;
goto block_27;
}
else
{
if (x_35 == 0)
{
lean_object* x_37; 
lean_free_object(x_16);
x_37 = lean_box(0);
x_22 = x_37;
goto block_27;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 0, x_4);
x_38 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_33);
lean_free_object(x_16);
x_40 = lean_box(0);
x_22 = x_40;
goto block_27;
}
}
else
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_41; 
lean_dec(x_30);
lean_free_object(x_16);
x_41 = lean_box(0);
x_22 = x_41;
goto block_27;
}
else
{
if (x_34 == 0)
{
lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_30);
lean_free_object(x_16);
x_42 = lean_box(0);
x_22 = x_42;
goto block_27;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_free_object(x_16);
x_46 = lean_box(0);
x_22 = x_46;
goto block_27;
}
else
{
if (x_35 == 0)
{
lean_object* x_47; 
lean_free_object(x_16);
x_47 = lean_box(0);
x_22 = x_47;
goto block_27;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 0, x_4);
x_48 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
x_23 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_20, x_21, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_12, x_24);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_7;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
x_64 = l_Lean_Meta_TransparencyMode_beq(x_58, x_61);
x_65 = lean_expr_eqv(x_59, x_62);
lean_dec(x_62);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
if (lean_obj_tag(x_63) == 0)
{
if (x_64 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_52 = x_66;
goto block_57;
}
else
{
if (x_65 == 0)
{
lean_object* x_67; 
x_67 = lean_box(0);
x_52 = x_67;
goto block_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_7);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_18, x_12, x_68);
lean_dec(x_12);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_63);
x_71 = lean_box(0);
x_52 = x_71;
goto block_57;
}
}
else
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_72; 
lean_dec(x_60);
x_72 = lean_box(0);
x_52 = x_72;
goto block_57;
}
else
{
if (x_64 == 0)
{
lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_60);
x_73 = lean_box(0);
x_52 = x_73;
goto block_57;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
lean_dec(x_60);
x_75 = lean_ctor_get(x_63, 0);
lean_inc(x_75);
lean_dec(x_63);
x_76 = lean_nat_dec_eq(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_52 = x_77;
goto block_57;
}
else
{
if (x_65 == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_52 = x_78;
goto block_57;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_7);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_18, x_12, x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
block_57:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
x_53 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_50, x_51, x_4, x_5);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_array_fset(x_18, x_12, x_54);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_7;
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
case 1:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_16);
if (x_82 == 0)
{
lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = x_2 >> x_9;
x_85 = x_3 + x_8;
x_86 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_83, x_84, x_85, x_4, x_5);
lean_ctor_set(x_16, 0, x_86);
x_87 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_7;
}
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_16, 0);
lean_inc(x_89);
lean_dec(x_16);
x_90 = x_2 >> x_9;
x_91 = x_3 + x_8;
x_92 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_89, x_90, x_91, x_4, x_5);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_array_fset(x_18, x_12, x_93);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_95 = lean_alloc_ctor(0, 1, 0);
} else {
 x_95 = x_7;
}
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_5);
x_97 = lean_array_fset(x_18, x_12, x_96);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_7;
}
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_1);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; size_t x_102; uint8_t x_103; 
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__8(x_1, x_100, x_4, x_5);
x_102 = 7;
x_103 = x_102 <= x_3;
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_101);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_dec_lt(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_110 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(x_3, x_107, x_108, lean_box(0), x_100, x_109);
lean_dec(x_108);
lean_dec(x_107);
return x_110;
}
else
{
return x_101;
}
}
else
{
return x_101;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_1, 0);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_1);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__8(x_113, x_114, x_4, x_5);
x_116 = 7;
x_117 = x_116 <= x_3;
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_115);
x_119 = lean_unsigned_to_nat(4u);
x_120 = lean_nat_dec_lt(x_118, x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_dec(x_115);
x_123 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_124 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(x_3, x_121, x_122, lean_box(0), x_114, x_123);
lean_dec(x_122);
lean_dec(x_121);
return x_124;
}
else
{
return x_115;
}
}
else
{
return x_115;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 1;
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = l_Lean_Meta_TransparencyMode_hash(x_10);
x_14 = l_Lean_Expr_hash(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = 11;
x_16 = lean_usize_mix_hash(x_14, x_15);
x_17 = lean_usize_mix_hash(x_13, x_16);
x_18 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_5, x_17, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 13;
x_22 = lean_usize_mix_hash(x_20, x_21);
x_23 = lean_usize_mix_hash(x_14, x_22);
x_24 = lean_usize_mix_hash(x_13, x_23);
x_25 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_5, x_24, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = 1;
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = l_Lean_Meta_TransparencyMode_hash(x_31);
x_35 = l_Lean_Expr_hash(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = 11;
x_37 = lean_usize_mix_hash(x_35, x_36);
x_38 = lean_usize_mix_hash(x_34, x_37);
x_39 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_26, x_38, x_28, x_2, x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = 13;
x_44 = lean_usize_mix_hash(x_42, x_43);
x_45 = lean_usize_mix_hash(x_35, x_44);
x_46 = lean_usize_mix_hash(x_34, x_45);
x_47 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_26, x_46, x_28, x_2, x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_4, x_5, x_6, x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
x_20 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_12);
lean_inc(x_5);
x_21 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_5, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_22);
x_32 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_31, x_18, x_22);
lean_ctor_set(x_26, 1, x_32);
x_33 = lean_st_ref_set(x_5, x_25, x_27);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_22);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 2);
x_40 = lean_ctor_get(x_26, 3);
x_41 = lean_ctor_get(x_26, 4);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_42);
lean_inc(x_38);
lean_dec(x_26);
lean_inc(x_22);
x_43 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_42, x_18, x_22);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_25, 1, x_44);
x_45 = lean_st_ref_set(x_5, x_25, x_27);
lean_dec(x_5);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 2);
x_51 = lean_ctor_get(x_25, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_52 = lean_ctor_get(x_26, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_26, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_26, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_26, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 x_57 = x_26;
} else {
 lean_dec_ref(x_26);
 x_57 = lean_box(0);
}
lean_inc(x_22);
x_58 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_56, x_18, x_22);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_50);
lean_ctor_set(x_60, 3, x_51);
x_61 = lean_st_ref_set(x_5, x_60, x_27);
lean_dec(x_5);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_22);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_18);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_21);
if (x_65 == 0)
{
return x_21;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_21, 0);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_21);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_ctor_get(x_20, 0);
lean_inc(x_69);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_69);
return x_12;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_12, 0);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_12);
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_dec(x_10);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_2);
x_75 = lean_unbox(x_70);
lean_dec(x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_75);
x_76 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_73, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_inc(x_5);
x_77 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_71);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_take(x_5, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 3);
lean_inc(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_93 = x_82;
} else {
 lean_dec_ref(x_82);
 x_93 = lean_box(0);
}
lean_inc(x_78);
x_94 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_92, x_74, x_78);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_89);
lean_ctor_set(x_95, 3, x_90);
lean_ctor_set(x_95, 4, x_91);
if (lean_is_scalar(x_87)) {
 x_96 = lean_alloc_ctor(0, 4, 0);
} else {
 x_96 = x_87;
}
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_85);
lean_ctor_set(x_96, 3, x_86);
x_97 = lean_st_ref_set(x_5, x_96, x_83);
lean_dec(x_5);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_78);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_74);
lean_dec(x_5);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_76, 0);
lean_inc(x_105);
lean_dec(x_76);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_71);
return x_106;
}
}
}
}
lean_object* l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_1);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_4(x_9, x_1, x_11, x_13, x_2);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_5(x_3, x_1, x_15, x_16, x_18, x_2);
return x_19;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_6(x_5, x_1, x_20, x_21, x_22, x_24, x_2);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_6(x_4, x_1, x_26, x_27, x_28, x_30, x_2);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_7(x_6, x_1, x_32, x_33, x_34, x_35, x_37, x_2);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_8, x_39, x_40, x_42, x_2);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_5(x_7, x_44, x_45, x_46, x_48, x_2);
return x_49;
}
default: 
{
lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_apply_2(x_10, x_1, x_2);
return x_50;
}
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_match__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_expr_eqv(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_push(x_3, x_6);
return x_8;
}
else
{
lean_dec(x_6);
return x_3;
}
}
}
case 5:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_Expr_hasFVar(x_2);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_9, x_3);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
}
case 6:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = l_Lean_Expr_hasFVar(x_2);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_14, x_3);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
case 7:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = l_Lean_Expr_hasFVar(x_2);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_19, x_3);
x_2 = x_20;
x_3 = x_22;
goto _start;
}
}
case 8:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = l_Lean_Expr_hasFVar(x_2);
if (x_27 == 0)
{
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_24, x_3);
x_29 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_25, x_28);
x_2 = x_26;
x_3 = x_29;
goto _start;
}
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_2, 1);
x_2 = x_31;
goto _start;
}
case 11:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_2, 2);
x_2 = x_33;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_instInhabitedNat;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_41 = l_instInhabitedNat;
x_42 = lean_array_get(x_41, x_1, x_16);
x_43 = lean_array_get(x_41, x_1, x_2);
x_44 = lean_nat_dec_lt(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
x_17 = x_1;
goto block_40;
}
else
{
lean_object* x_45; 
x_45 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_45;
goto block_40;
}
block_40:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_instInhabitedNat;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_nat_dec_lt(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get(x_18, x_17, x_16);
x_23 = lean_nat_dec_lt(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = l_Lean_Position_lt___closed__2;
lean_inc_n(x_2, 2);
x_25 = l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(x_24, x_3, x_19, x_17, x_2, x_2);
x_4 = x_25;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_26 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_27 = lean_array_get(x_18, x_26, x_3);
x_28 = l_Lean_Position_lt___closed__2;
lean_inc_n(x_2, 2);
x_29 = l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(x_28, x_3, x_27, x_26, x_2, x_2);
x_4 = x_29;
goto block_12;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_19);
x_30 = lean_array_swap(x_17, x_2, x_3);
x_31 = lean_array_get(x_18, x_30, x_16);
x_32 = lean_array_get(x_18, x_30, x_3);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_34 = l_Lean_Position_lt___closed__2;
lean_inc_n(x_2, 2);
x_35 = l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(x_34, x_3, x_32, x_30, x_2, x_2);
x_4 = x_35;
goto block_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_36 = lean_array_swap(x_30, x_16, x_3);
lean_dec(x_16);
x_37 = lean_array_get(x_18, x_36, x_3);
x_38 = l_Lean_Position_lt___closed__2;
lean_inc_n(x_2, 2);
x_39 = l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(x_38, x_3, x_37, x_36, x_2, x_2);
x_4 = x_39;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_4, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
lean_object* l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 2);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_nat_add(x_5, x_10);
if (x_15 == 0)
{
uint8_t x_18; 
x_18 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_2, x_5);
lean_dec(x_5);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_17;
x_6 = lean_box(0);
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = 1;
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 2, x_23);
x_24 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_17;
x_6 = lean_box(0);
x_7 = x_24;
goto _start;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_26);
x_28 = lean_array_push(x_7, x_27);
x_4 = x_11;
x_5 = x_17;
x_6 = lean_box(0);
x_7 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_16);
lean_dec(x_5);
x_30 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_17;
x_6 = lean_box(0);
x_7 = x_30;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(x_1, x_2, x_1, x_6, x_4, lean_box(0), x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_le(x_11, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = l_Lean_Expr_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_1, x_4);
lean_inc(x_6);
x_19 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(x_18, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_23 = lean_box(0);
x_3 = x_16;
x_4 = x_22;
x_5 = x_23;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_box(0);
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_1, x_11, x_8, x_9, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
x_17 = l_Array_empty___closed__1;
x_18 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_17, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
x_22 = l_Array_empty___closed__1;
x_23 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_22, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getTransparency___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_3, x_4, x_5, x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 1;
lean_ctor_set_uint8(x_21, 5, x_27);
x_28 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
lean_inc(x_4);
x_29 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_22, x_2, x_28, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_take(x_4, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_30);
x_40 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_39, x_17, x_30);
lean_ctor_set(x_34, 1, x_40);
x_41 = lean_st_ref_set(x_4, x_33, x_35);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_30);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 2);
x_48 = lean_ctor_get(x_34, 3);
x_49 = lean_ctor_get(x_34, 4);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_50);
lean_inc(x_46);
lean_dec(x_34);
lean_inc(x_30);
x_51 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_50, x_17, x_30);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_49);
lean_ctor_set(x_33, 1, x_52);
x_53 = lean_st_ref_set(x_4, x_33, x_35);
lean_dec(x_4);
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
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_30);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 2);
x_59 = lean_ctor_get(x_33, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
x_60 = lean_ctor_get(x_34, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_34, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_34, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_34, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_34, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 x_65 = x_34;
} else {
 lean_dec_ref(x_34);
 x_65 = lean_box(0);
}
lean_inc(x_30);
x_66 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_64, x_17, x_30);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set(x_67, 4, x_63);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_58);
lean_ctor_set(x_68, 3, x_59);
x_69 = lean_st_ref_set(x_4, x_68, x_35);
lean_dec(x_4);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_30);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_17);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
return x_29;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_29, 0);
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_29);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get_uint8(x_21, 0);
x_78 = lean_ctor_get_uint8(x_21, 1);
x_79 = lean_ctor_get_uint8(x_21, 2);
x_80 = lean_ctor_get_uint8(x_21, 3);
x_81 = lean_ctor_get_uint8(x_21, 4);
x_82 = lean_ctor_get_uint8(x_21, 6);
x_83 = lean_ctor_get_uint8(x_21, 7);
lean_dec(x_21);
x_84 = 1;
x_85 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_85, 0, x_77);
lean_ctor_set_uint8(x_85, 1, x_78);
lean_ctor_set_uint8(x_85, 2, x_79);
lean_ctor_set_uint8(x_85, 3, x_80);
lean_ctor_set_uint8(x_85, 4, x_81);
lean_ctor_set_uint8(x_85, 5, x_84);
lean_ctor_set_uint8(x_85, 6, x_82);
lean_ctor_set_uint8(x_85, 7, x_83);
lean_ctor_set(x_3, 0, x_85);
x_86 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
lean_inc(x_4);
x_87 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_22, x_2, x_86, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_take(x_4, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
 x_103 = lean_box(0);
}
lean_inc(x_88);
x_104 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_102, x_17, x_88);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_99);
lean_ctor_set(x_105, 3, x_100);
lean_ctor_set(x_105, 4, x_101);
if (lean_is_scalar(x_97)) {
 x_106 = lean_alloc_ctor(0, 4, 0);
} else {
 x_106 = x_97;
}
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_95);
lean_ctor_set(x_106, 3, x_96);
x_107 = lean_st_ref_set(x_4, x_106, x_93);
lean_dec(x_4);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_88);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_17);
lean_dec(x_4);
x_111 = lean_ctor_get(x_87, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_87, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_113 = x_87;
} else {
 lean_dec_ref(x_87);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_115 = lean_ctor_get(x_3, 1);
x_116 = lean_ctor_get(x_3, 2);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_3);
x_117 = lean_ctor_get_uint8(x_21, 0);
x_118 = lean_ctor_get_uint8(x_21, 1);
x_119 = lean_ctor_get_uint8(x_21, 2);
x_120 = lean_ctor_get_uint8(x_21, 3);
x_121 = lean_ctor_get_uint8(x_21, 4);
x_122 = lean_ctor_get_uint8(x_21, 6);
x_123 = lean_ctor_get_uint8(x_21, 7);
if (lean_is_exclusive(x_21)) {
 x_124 = x_21;
} else {
 lean_dec_ref(x_21);
 x_124 = lean_box(0);
}
x_125 = 1;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 0, 8);
} else {
 x_126 = x_124;
}
lean_ctor_set_uint8(x_126, 0, x_117);
lean_ctor_set_uint8(x_126, 1, x_118);
lean_ctor_set_uint8(x_126, 2, x_119);
lean_ctor_set_uint8(x_126, 3, x_120);
lean_ctor_set_uint8(x_126, 4, x_121);
lean_ctor_set_uint8(x_126, 5, x_125);
lean_ctor_set_uint8(x_126, 6, x_122);
lean_ctor_set_uint8(x_126, 7, x_123);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_115);
lean_ctor_set(x_127, 2, x_116);
x_128 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
lean_inc(x_4);
x_129 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_22, x_2, x_128, x_127, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_st_ref_take(x_4, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 3);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_134, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_134, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 x_145 = x_134;
} else {
 lean_dec_ref(x_134);
 x_145 = lean_box(0);
}
lean_inc(x_130);
x_146 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_144, x_17, x_130);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 5, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_141);
lean_ctor_set(x_147, 3, x_142);
lean_ctor_set(x_147, 4, x_143);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 4, 0);
} else {
 x_148 = x_139;
}
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_137);
lean_ctor_set(x_148, 3, x_138);
x_149 = lean_st_ref_set(x_4, x_148, x_135);
lean_dec(x_4);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_130);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_17);
lean_dec(x_4);
x_153 = lean_ctor_get(x_129, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_129, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_155 = x_129;
} else {
 lean_dec_ref(x_129);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_20);
if (x_157 == 0)
{
return x_20;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_20, 0);
x_159 = lean_ctor_get(x_20, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_20);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_19, 0);
lean_inc(x_161);
lean_dec(x_19);
lean_ctor_set(x_11, 0, x_161);
return x_11;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_11, 0);
x_163 = lean_ctor_get(x_11, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_11);
x_164 = lean_ctor_get(x_9, 1);
lean_inc(x_164);
lean_dec(x_9);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
lean_inc(x_2);
lean_inc(x_1);
x_166 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
x_167 = lean_unbox(x_162);
lean_dec(x_162);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_167);
x_168 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_165, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_169 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_170 = lean_ctor_get(x_3, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_ctor_get(x_3, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_3, 2);
lean_inc(x_174);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_175 = x_3;
} else {
 lean_dec_ref(x_3);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get_uint8(x_170, 0);
x_177 = lean_ctor_get_uint8(x_170, 1);
x_178 = lean_ctor_get_uint8(x_170, 2);
x_179 = lean_ctor_get_uint8(x_170, 3);
x_180 = lean_ctor_get_uint8(x_170, 4);
x_181 = lean_ctor_get_uint8(x_170, 6);
x_182 = lean_ctor_get_uint8(x_170, 7);
if (lean_is_exclusive(x_170)) {
 x_183 = x_170;
} else {
 lean_dec_ref(x_170);
 x_183 = lean_box(0);
}
x_184 = 1;
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 0, 8);
} else {
 x_185 = x_183;
}
lean_ctor_set_uint8(x_185, 0, x_176);
lean_ctor_set_uint8(x_185, 1, x_177);
lean_ctor_set_uint8(x_185, 2, x_178);
lean_ctor_set_uint8(x_185, 3, x_179);
lean_ctor_set_uint8(x_185, 4, x_180);
lean_ctor_set_uint8(x_185, 5, x_184);
lean_ctor_set_uint8(x_185, 6, x_181);
lean_ctor_set_uint8(x_185, 7, x_182);
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(0, 3, 0);
} else {
 x_186 = x_175;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_173);
lean_ctor_set(x_186, 2, x_174);
x_187 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
lean_inc(x_4);
x_188 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_171, x_2, x_187, x_186, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_st_ref_take(x_4, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_193, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_193, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 x_204 = x_193;
} else {
 lean_dec_ref(x_193);
 x_204 = lean_box(0);
}
lean_inc(x_189);
x_205 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_203, x_166, x_189);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 5, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_200);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set(x_206, 4, x_202);
if (lean_is_scalar(x_198)) {
 x_207 = lean_alloc_ctor(0, 4, 0);
} else {
 x_207 = x_198;
}
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_196);
lean_ctor_set(x_207, 3, x_197);
x_208 = lean_st_ref_set(x_4, x_207, x_194);
lean_dec(x_4);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_189);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_166);
lean_dec(x_4);
x_212 = lean_ctor_get(x_188, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_188, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_214 = x_188;
} else {
 lean_dec_ref(x_188);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_ctor_get(x_169, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_169, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_218 = x_169;
} else {
 lean_dec_ref(x_169);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_168, 0);
lean_inc(x_220);
lean_dec(x_168);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_163);
return x_221;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_getFunInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_FunInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
