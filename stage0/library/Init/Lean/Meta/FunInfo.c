// Lean compiler output
// Module: Init.Lean.Meta.FunInfo
// Imports: Init.Lean.Meta.Basic Init.Lean.Meta.InferType
#include "runtime/lean.h"
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
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectDeps(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Nat_foldMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_PersistentHashMap_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_InfoCacheKey_Hashable___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_HasBeq___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
extern lean_object* l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
lean_object* l_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectDepsAux(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_collectDepsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_inferTypeAuxAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whenHasVar(lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1;
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2;
lean_object* l_Lean_Meta_whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_Lean_Meta_collectDepsAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___boxed(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_collectDepsAux___main___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_18;
goto _start;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_20; 
x_20 = lean_expr_eqv(x_11, x_14);
lean_dec(x_14);
if (x_20 == 0)
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
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_14);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_4, x_29);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_15);
lean_dec(x_14);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
x_39 = lean_expr_eqv(x_11, x_14);
lean_dec(x_14);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_15);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_43; 
x_43 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
lean_ctor_set(x_15, 0, x_43);
return x_15;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_15, 0);
lean_inc(x_45);
lean_dec(x_15);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_4, x_47);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_48;
goto _start;
}
else
{
uint8_t x_50; 
x_50 = lean_expr_eqv(x_11, x_14);
lean_dec(x_14);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_4, x_51);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_52;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
x_20 = lean_box(0);
return x_20;
}
else
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_21; 
x_21 = lean_expr_eqv(x_14, x_17);
lean_dec(x_17);
if (x_21 == 0)
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
else
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
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
lean_dec(x_17);
lean_dec(x_12);
x_25 = lean_box(0);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_12);
x_30 = lean_box(0);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_expr_eqv(x_14, x_17);
lean_dec(x_17);
if (x_31 == 0)
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
lean_dec(x_17);
lean_dec(x_12);
x_36 = lean_box(0);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_expr_eqv(x_14, x_17);
lean_dec(x_17);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_12);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_12);
return x_39;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_40; size_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
x_41 = x_2 >> x_5;
x_42 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(x_40, x_41, x_3);
lean_dec(x_40);
return x_42;
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(x_44, x_45, lean_box(0), x_46, x_3);
return x_47;
}
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_TransparencyMode_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
x_9 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_6);
x_10 = lean_usize_mix_hash(x_8, x_9);
x_11 = lean_usize_mix_hash(x_7, x_10);
x_12 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(x_3, x_11, x_2);
return x_12;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
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
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
else
{
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_33; 
x_33 = lean_expr_eqv(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
if (x_33 == 0)
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
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
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
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
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
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_2, x_47);
lean_dec(x_2);
x_2 = x_48;
goto _start;
}
else
{
uint8_t x_50; 
x_50 = lean_expr_eqv(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_2, x_51);
lean_dec(x_2);
x_2 = x_52;
goto _start;
}
else
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_box(0);
x_17 = x_54;
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_9 = lean_array_fget(x_4, x_5);
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
x_22 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_19);
lean_dec(x_19);
x_23 = lean_usize_mix_hash(x_21, x_22);
x_24 = lean_usize_mix_hash(x_20, x_23);
x_25 = x_24 >> x_14;
x_26 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_6, x_25, x_1, x_9, x_10);
x_5 = x_16;
x_6 = x_26;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
x_27 = l_Lean_Meta_TransparencyMode_beq(x_21, x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
x_28 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_fset(x_17, x_12, x_29);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_31; 
x_31 = lean_expr_eqv(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_15);
x_32 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_array_fset(x_17, x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_35 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_free_object(x_15);
x_36 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_array_fset(x_17, x_12, x_37);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_38);
return x_1;
}
}
else
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
x_39 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_array_fset(x_17, x_12, x_40);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_25);
lean_dec(x_22);
lean_free_object(x_15);
x_45 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
uint8_t x_48; 
x_48 = lean_expr_eqv(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_15);
x_49 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_array_fset(x_17, x_12, x_50);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
lean_object* x_52; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_52 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_53, sizeof(void*)*2);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
x_61 = l_Lean_Meta_TransparencyMode_beq(x_55, x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
x_62 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_array_fset(x_17, x_12, x_63);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_64);
return x_1;
}
else
{
if (lean_obj_tag(x_57) == 0)
{
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_65; 
x_65 = lean_expr_eqv(x_56, x_59);
lean_dec(x_59);
lean_dec(x_56);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_array_fset(x_17, x_12, x_67);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_53);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_5);
x_70 = lean_array_fset(x_17, x_12, x_69);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_70);
return x_1;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_56);
x_71 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_array_fset(x_17, x_12, x_72);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_73);
return x_1;
}
}
else
{
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
x_74 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_array_fset(x_17, x_12, x_75);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_76);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_57, 0);
lean_inc(x_77);
lean_dec(x_57);
x_78 = lean_ctor_get(x_60, 0);
lean_inc(x_78);
lean_dec(x_60);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_59);
lean_dec(x_56);
x_80 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_array_fset(x_17, x_12, x_81);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_82);
return x_1;
}
else
{
uint8_t x_83; 
x_83 = lean_expr_eqv(x_56, x_59);
lean_dec(x_59);
lean_dec(x_56);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_array_fset(x_17, x_12, x_85);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_86);
return x_1;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_54);
lean_dec(x_53);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_4);
lean_ctor_set(x_87, 1, x_5);
x_88 = lean_array_fset(x_17, x_12, x_87);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_88);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_15);
if (x_89 == 0)
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_15, 0);
x_91 = x_2 >> x_9;
x_92 = x_3 + x_8;
x_93 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_90, x_91, x_92, x_4, x_5);
lean_ctor_set(x_15, 0, x_93);
x_94 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
else
{
lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_15, 0);
lean_inc(x_95);
lean_dec(x_15);
x_96 = x_2 >> x_9;
x_97 = x_3 + x_8;
x_98 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_95, x_96, x_97, x_4, x_5);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_array_fset(x_17, x_12, x_99);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_100);
return x_1;
}
}
default: 
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_4);
lean_ctor_set(x_101, 1, x_5);
x_102 = lean_array_fset(x_17, x_12, x_101);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_102);
return x_1;
}
}
}
}
else
{
lean_object* x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
lean_dec(x_1);
x_104 = 1;
x_105 = 5;
x_106 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_107 = x_2 & x_106;
x_108 = lean_usize_to_nat(x_107);
x_109 = lean_array_get_size(x_103);
x_110 = lean_nat_dec_lt(x_108, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_5);
lean_dec(x_4);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_103);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_array_fget(x_103, x_108);
x_113 = lean_box(2);
x_114 = lean_array_fset(x_103, x_108, x_113);
switch (lean_obj_tag(x_112)) {
case 0:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_117 = x_112;
} else {
 lean_dec_ref(x_112);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_119 = lean_ctor_get(x_4, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_115, sizeof(void*)*2);
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
x_124 = l_Lean_Meta_TransparencyMode_beq(x_118, x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_117);
x_125 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_array_fset(x_114, x_108, x_126);
lean_dec(x_108);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_129; 
x_129 = lean_expr_eqv(x_119, x_122);
lean_dec(x_122);
lean_dec(x_119);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
x_130 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_array_fset(x_114, x_108, x_131);
lean_dec(x_108);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_116);
lean_dec(x_115);
if (lean_is_scalar(x_117)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_117;
}
lean_ctor_set(x_134, 0, x_4);
lean_ctor_set(x_134, 1, x_5);
x_135 = lean_array_fset(x_114, x_108, x_134);
lean_dec(x_108);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_117);
x_137 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_array_fset(x_114, x_108, x_138);
lean_dec(x_108);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
else
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_117);
x_141 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_array_fset(x_114, x_108, x_142);
lean_dec(x_108);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_120, 0);
lean_inc(x_145);
lean_dec(x_120);
x_146 = lean_ctor_get(x_123, 0);
lean_inc(x_146);
lean_dec(x_123);
x_147 = lean_nat_dec_eq(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_117);
x_148 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_array_fset(x_114, x_108, x_149);
lean_dec(x_108);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lean_expr_eqv(x_119, x_122);
lean_dec(x_122);
lean_dec(x_119);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_117);
x_153 = l_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_array_fset(x_114, x_108, x_154);
lean_dec(x_108);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_116);
lean_dec(x_115);
if (lean_is_scalar(x_117)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_117;
}
lean_ctor_set(x_157, 0, x_4);
lean_ctor_set(x_157, 1, x_5);
x_158 = lean_array_fset(x_114, x_108, x_157);
lean_dec(x_108);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
}
}
}
case 1:
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_112, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_161 = x_112;
} else {
 lean_dec_ref(x_112);
 x_161 = lean_box(0);
}
x_162 = x_2 >> x_105;
x_163 = x_3 + x_104;
x_164 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_160, x_162, x_163, x_4, x_5);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_array_fset(x_114, x_108, x_165);
lean_dec(x_108);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
default: 
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_4);
lean_ctor_set(x_168, 1, x_5);
x_169 = lean_array_fset(x_114, x_108, x_168);
lean_dec(x_108);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; size_t x_173; uint8_t x_174; 
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(x_1, x_171, x_4, x_5);
x_173 = 7;
x_174 = x_173 <= x_3;
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_172);
x_176 = lean_unsigned_to_nat(4u);
x_177 = lean_nat_dec_lt(x_175, x_176);
lean_dec(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_dec(x_172);
x_180 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_181 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(x_3, x_178, x_179, x_178, x_171, x_180);
lean_dec(x_179);
lean_dec(x_178);
return x_181;
}
else
{
return x_172;
}
}
else
{
return x_172;
}
}
}
}
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_Hashable___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_HasBeq___boxed), 2, 0);
return x_1;
}
}
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
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
x_15 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_12);
lean_dec(x_12);
x_16 = lean_usize_mix_hash(x_14, x_15);
x_17 = lean_usize_mix_hash(x_13, x_16);
x_18 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_5, x_17, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = 1;
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_20, x_22);
lean_dec(x_20);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = l_Lean_Meta_TransparencyMode_hash(x_24);
x_28 = l_Lean_Expr_hash(x_25);
lean_dec(x_25);
x_29 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_26);
lean_dec(x_26);
x_30 = lean_usize_mix_hash(x_28, x_29);
x_31 = lean_usize_mix_hash(x_27, x_30);
x_32 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_19, x_31, x_21, x_2, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
x_11 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_apply_2(x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 2);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_22 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_21, x_10, x_16);
lean_ctor_set(x_14, 1, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_16);
x_25 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_24, x_10, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_13, 2, x_26);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get(x_13, 4);
x_31 = lean_ctor_get(x_13, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_34 = x_14;
} else {
 lean_dec_ref(x_14);
 x_34 = lean_box(0);
}
lean_inc(x_16);
x_35 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_33, x_10, x_16);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 4, x_30);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_12, 1, x_37);
return x_12;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_ctor_get(x_13, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_13, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 5);
lean_inc(x_43);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_44 = x_13;
} else {
 lean_dec_ref(x_13);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_47 = x_14;
} else {
 lean_dec_ref(x_14);
 x_47 = lean_box(0);
}
lean_inc(x_38);
x_48 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_46, x_10, x_38);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_5);
return x_57;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_whenHasVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_whenHasVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_whenHasVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whenHasVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_whenHasVar___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_nat_dec_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_collectDepsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1(x_1, x_2, x_4);
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
x_7 = l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2(x_3, x_6);
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
x_12 = l_Lean_Meta_collectDepsAux___main(x_1, x_9, x_3);
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
x_17 = l_Lean_Meta_collectDepsAux___main(x_1, x_14, x_3);
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
x_22 = l_Lean_Meta_collectDepsAux___main(x_1, x_19, x_3);
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
x_28 = l_Lean_Meta_collectDepsAux___main(x_1, x_24, x_3);
x_29 = l_Lean_Meta_collectDepsAux___main(x_1, x_25, x_28);
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
lean_object* l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___main___at_Lean_Meta_collectDepsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_collectDepsAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_collectDepsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_collectDepsAux___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_collectDepsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_collectDepsAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_collectDepsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_collectDepsAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Nat_Inhabited;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = lean_nat_dec_lt(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_swap(x_3, x_4, x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_18 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_37 = l_Nat_Inhabited;
x_38 = lean_array_get(x_37, x_1, x_16);
x_39 = lean_array_get(x_37, x_1, x_2);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
x_17 = x_1;
goto block_36;
}
else
{
lean_object* x_41; 
x_41 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_41;
goto block_36;
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Nat_Inhabited;
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
lean_object* x_24; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_24 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_24;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_25 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_26 = lean_array_get(x_18, x_25, x_3);
lean_inc_n(x_2, 2);
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(x_3, x_26, x_25, x_2, x_2);
lean_dec(x_26);
x_4 = x_27;
goto block_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_28 = lean_array_swap(x_17, x_2, x_3);
x_29 = lean_array_get(x_18, x_28, x_16);
x_30 = lean_array_get(x_18, x_28, x_3);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(x_3, x_30, x_28, x_2, x_2);
lean_dec(x_30);
x_4 = x_32;
goto block_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_33 = lean_array_swap(x_28, x_16, x_3);
lean_dec(x_16);
x_34 = lean_array_get(x_18, x_33, x_3);
lean_inc_n(x_2, 2);
x_35 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(x_3, x_34, x_33, x_2, x_2);
lean_dec(x_34);
x_4 = x_35;
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
x_8 = l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1(x_6, x_2, x_5);
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
lean_object* l_Lean_Meta_collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Meta_collectDepsAux___main(x_1, x_2, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1(x_4, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_collectDeps___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Meta_collectDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
if (x_15 == 0)
{
uint8_t x_19; 
x_19 = l_Array_contains___at_Lean_Meta_collectDepsAux___main___spec__2(x_1, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_inc(x_8);
x_20 = x_8;
x_21 = lean_array_fset(x_11, x_2, x_20);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_12);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 2, x_14);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 3, x_23);
x_25 = x_24;
x_26 = lean_array_fset(x_11, x_2, x_25);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
lean_inc(x_8);
x_28 = x_8;
x_29 = lean_array_fset(x_11, x_2, x_28);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_29;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1(x_2, x_4, x_1);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Expr_Inhabited;
x_8 = lean_array_get(x_7, x_1, x_3);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
x_10 = l_Lean_Meta_getLocalDecl(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_inc(x_13);
x_14 = l_Lean_Meta_isPropAux(x_2, x_13, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Meta_collectDeps(x_1, x_13);
lean_dec(x_13);
x_18 = l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(x_4, x_17);
x_19 = l_Lean_LocalDecl_binderInfo(x_11);
lean_dec(x_11);
x_20 = 1;
x_21 = l_Lean_BinderInfo_beq(x_19, x_20);
x_22 = 3;
x_23 = l_Lean_BinderInfo_beq(x_19, x_22);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_23);
x_26 = lean_unbox(x_16);
lean_dec(x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_26);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 3, x_24);
x_27 = lean_array_push(x_18, x_25);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = l_Lean_Meta_collectDeps(x_1, x_13);
lean_dec(x_13);
x_31 = l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(x_4, x_30);
x_32 = l_Lean_LocalDecl_binderInfo(x_11);
lean_dec(x_11);
x_33 = 1;
x_34 = l_Lean_BinderInfo_beq(x_32, x_33);
x_35 = 3;
x_36 = l_Lean_BinderInfo_beq(x_32, x_35);
x_37 = 0;
x_38 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 1, x_36);
x_39 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 3, x_37);
x_40 = lean_array_push(x_31, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
return x_10;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoAuxAux___lambda__1___boxed), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_array_get_size(x_3);
x_9 = l_Array_empty___closed__1;
lean_inc(x_8);
x_10 = l_Nat_foldMAux___main___rarg(x_2, x_7, x_8, x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_2(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Meta_collectDeps(x_3, x_4);
lean_dec(x_3);
x_15 = l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = l_Lean_Meta_collectDeps(x_3, x_4);
lean_dec(x_3);
x_20 = l___private_Init_Lean_Meta_FunInfo_2__updateHasFwdDeps(x_17, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_getFunInfoAuxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
x_11 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2;
x_12 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1;
lean_inc(x_10);
x_13 = l_PersistentHashMap_find___rarg(x_11, x_12, x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_usingDefault), 4, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_4);
lean_inc(x_14);
x_15 = l_Lean_Meta_inferTypeAuxAux___main(x_14, x_2, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Init_Lean_Meta_InferType_1__getForallResultType___closed__1;
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoAuxAux___lambda__2___boxed), 6, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_forallBoundedTelescope___rarg(x_14, x_16, x_3, x_19, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 2);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_30 = l_PersistentHashMap_insert___rarg(x_11, x_12, x_29, x_10, x_24);
lean_ctor_set(x_22, 1, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
lean_inc(x_24);
x_33 = l_PersistentHashMap_insert___rarg(x_11, x_12, x_32, x_10, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_21, 2, x_34);
return x_20;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
x_37 = lean_ctor_get(x_21, 3);
x_38 = lean_ctor_get(x_21, 4);
x_39 = lean_ctor_get(x_21, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_42 = x_22;
} else {
 lean_dec_ref(x_22);
 x_42 = lean_box(0);
}
lean_inc(x_24);
x_43 = l_PersistentHashMap_insert___rarg(x_11, x_12, x_41, x_10, x_24);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_37);
lean_ctor_set(x_45, 4, x_38);
lean_ctor_set(x_45, 5, x_39);
lean_ctor_set(x_20, 1, x_45);
return x_20;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_21, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_21, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_21, 5);
lean_inc(x_51);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_52 = x_21;
} else {
 lean_dec_ref(x_21);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_55 = x_22;
} else {
 lean_dec_ref(x_22);
 x_55 = lean_box(0);
}
lean_inc(x_46);
x_56 = l_PersistentHashMap_insert___rarg(x_11, x_12, x_54, x_10, x_46);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_49);
lean_ctor_set(x_58, 4, x_50);
lean_ctor_set(x_58, 5, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_13, 0);
lean_inc(x_68);
lean_dec(x_13);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
return x_69;
}
}
}
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFunInfoAuxAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_getFunInfoAuxAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFunInfoAuxAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Meta_getFunInfoAuxAux(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_getFunInfoNArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = l_Lean_Meta_getFunInfoAuxAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_FunInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__1);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
